using BepInEx;
using BepInEx.Configuration;
using HarmonyLib;
using System;
using System.Collections;
using System.Collections.Generic;
using System.Diagnostics;
using System.Globalization;
using System.IO;
using System.IO.Compression;
using System.Net.Sockets;
using System.Reflection;
using System.Text;
using System.Text.RegularExpressions;
using System.Threading;
using System.Threading.Tasks;
using UnityEngine;
using UnityEngine.SceneManagement;

namespace OverlayHUD
{
    [BepInPlugin("local.overlay.overlay_hud", "OverlayHUD", "26.8.0")]
    public sealed class Plugin : BaseUnityPlugin
    {
        private static Plugin instance;
        private static readonly List<string> seenMonsters = new List<string>();
        private static readonly List<Component> knownEnemyParents = new List<Component>();
        private static readonly HashSet<int> sentEnemyInstanceIds = new HashSet<int>();
        private static readonly HashSet<int> valuablesInDollarHaul = new HashSet<int>();
        private static readonly object seenLock = new object();
        private static readonly object enemyLock = new object();
        private static readonly object reflectionCacheLock = new object();
        private static readonly object networkQueueLock = new object();

        // Оптимизированный кэш Рефлексии (Больше никаких лагов от сборщика мусора!)
        private static readonly Dictionary<Type, Dictionary<string, MemberInfo>> fastMemberCache = new Dictionary<Type, Dictionary<string, MemberInfo>>();
        private static readonly Dictionary<Type, Dictionary<string, MethodInfo>> fastNoArgMethodCache = new Dictionary<Type, Dictionary<string, MethodInfo>>();

        private static Task networkQueueTail = Task.CompletedTask;
        private static int latestMonsterStatusRequestVersion;
        private static int latestMapValueRequestVersion;
        private static float mapValue;
        private static float mapValueInitial;
        private static float lostValue;

        private static readonly Dictionary<string, string> KnownMonsters = new Dictionary<string, string>
        {
            { "apexpredator", "Apex Predator" }, { "animal", "Animal" }, { "banger", "Banger" },
            { "bang", "Banger" }, { "bella", "Bella" }, { "beamer", "Clown" },
            { "birthdayboy", "Birthday Boy" }, { "bowtie", "Bowtie" }, { "chef", "Chef" },
            { "cheffrog", "Chef" }, { "ceilingeye", "Peeper" }, { "cleanupcrew", "Cleanup Crew" },
            { "clown", "Clown" }, { "clownbeamer", "Clown" }, { "duck", "Rugrat" },
            { "elsa", "Elsa" }, { "floater", "Mentalist" }, { "gambit", "Gambit" },
            { "gnome", "Gnomes" }, { "headgrab", "Headgrab" }, { "headgrabber", "Headgrab" },
            { "headman", "Headman" }, { "hearthugger", "Heart Hugger" }, { "hidden", "Hidden" },
            { "huntsman", "Huntsman" }, { "hunter", "Huntsman" }, { "loom", "Loom" },
            { "mentalist", "Mentalist" }, { "oogly", "Oogly" }, { "peeper", "Peeper" },
            { "reaper", "Reaper" }, { "robe", "Robe" }, { "rugrat", "Rugrat" },
            { "runner", "Gambit" }, { "shadowchild", "Shadow Child" }, { "shadow", "Shadow Child" },
            { "spewer", "Spewer" }, { "slowmouth", "Spewer" }, { "slowwalker", "Trudge" },
            { "spinny", "Bowtie" }, { "thinman", "Reaper" }, { "tick", "Tick" },
            { "trudge", "Trudge" }, { "tricycle", "Birthday Boy" }, { "tumbler", "Apex Predator" },
            { "upscream", "Upscream" }, { "valuablethrower", "Rugrat" }
        };

        private static readonly KeyValuePair<string, string>[] TrackedPlayerUpgrades =
        {
            new KeyValuePair<string, string>("strength", "playerUpgradeStrength"),
            new KeyValuePair<string, string>("tumbleLaunch", "playerUpgradeLaunch"),
            new KeyValuePair<string, string>("range", "playerUpgradeRange"),
            new KeyValuePair<string, string>("sprintSpeed", "playerUpgradeSpeed"),
            new KeyValuePair<string, string>("tumbleWings", "playerUpgradeTumbleWings"),
            new KeyValuePair<string, string>("crouchRest", "playerUpgradeCrouchRest"),
            new KeyValuePair<string, string>("extraJump", "playerUpgradeExtraJump"),
            new KeyValuePair<string, string>("tumbleClimb", "playerUpgradeTumbleClimb"),
            new KeyValuePair<string, string>("health", "playerUpgradeHealth"),
            new KeyValuePair<string, string>("stamina", "playerUpgradeStamina"),
            new KeyValuePair<string, string>("mapPlayerCount", "playerUpgradeMapPlayerCount"),
            new KeyValuePair<string, string>("deathHeadBattery", "playerUpgradeDeathHeadBattery")
        };

        private static readonly Dictionary<string, string> UpgradeStateKeyByPunMethod = new Dictionary<string, string>
        {
            { "UpgradePlayerGrabStrength", "strength" }, { "UpgradePlayerTumbleLaunch", "tumbleLaunch" },
            { "UpgradePlayerGrabRange", "range" }, { "UpgradePlayerSprintSpeed", "sprintSpeed" },
            { "UpgradePlayerTumbleWings", "tumbleWings" }, { "UpgradePlayerCrouchRest", "crouchRest" },
            { "UpgradePlayerExtraJump", "extraJump" }, { "UpgradePlayerTumbleClimb", "tumbleClimb" },
            { "UpgradePlayerHealth", "health" }, { "UpgradePlayerEnergy", "stamina" },
            { "UpgradeMapPlayerCount", "mapPlayerCount" }, { "UpgradeDeathHeadBattery", "deathHeadBattery" }
        };

        private static readonly HashSet<string> PlayerVisionLegacyFallbackMonsters = new HashSet<string>(StringComparer.Ordinal) { "Tick", "Upscream" };
        private static readonly string[] CurrentHealthMemberNames = { "currentHealth", "healthCurrent", "_currentSyncedHealth", "_syncedHealth", "currentHP", "healthValue", "HealthValue" };
        private static readonly string[] MaxHealthMemberNames = { "maxHealth", "MaxHealth", "healthMax", "HealthMax", "healthMaximum", "maximumHealth", "maxHP", "HPMax", "health", "Health" };

        private readonly Dictionary<string, float> lastSeenLoggedAt = new Dictionary<string, float>();
        private readonly Dictionary<int, string> resolvedMonsterNames = new Dictionary<int, string>();
        private readonly Dictionary<int, int> sourceIdsByEnemyParent = new Dictionary<int, int>();
        private readonly Dictionary<int, bool> lastAliveBySourceId = new Dictionary<int, bool>();
        private readonly Dictionary<int, string> lastHealthDebugBySourceId = new Dictionary<int, string>();
        private readonly Dictionary<int, object[]> healthSourcesByRootId = new Dictionary<int, object[]>();
        private readonly Dictionary<int, string> lastImmediateStatusBySourceId = new Dictionary<int, string>();
        private readonly Dictionary<int, string> lastTimerStatusBySourceId = new Dictionary<int, string>();
        private readonly Dictionary<int, float> lastTimerStatusSentAtBySourceId = new Dictionary<int, float>();
        private readonly Dictionary<int, bool> enemyHasVisionByParentId = new Dictionary<int, bool>();
        private readonly Dictionary<int, bool> enemyHasOnScreenByParentId = new Dictionary<int, bool>();
        private readonly Dictionary<int, VisionEnemyCache> visionEnemyCacheByVisionId = new Dictionary<int, VisionEnemyCache>();
        private readonly HashSet<int> pendingEncounterIds = new HashSet<int>();

        private readonly Dictionary<int, float> clientSimulatedTimers = new Dictionary<int, float>();
        private readonly Dictionary<int, float> clientSimulatedHealth = new Dictionary<int, float>();

        private float nextScanAt, nextStatusSyncAt, nextUpgradeSyncAt, nextMapValueSyncAt, nextBroadEnemyDiscoveryAt, nextStatusDirectorRecoveryAt, scanPausedUntil;
        private int fallbackLevel = 1, lastSyncedLevel;
        private readonly Dictionary<string, int> lastSyncedUpgrades = new Dictionary<string, int>();
        private readonly HashSet<string> pendingUpgradeKeys = new HashSet<string>();
        private string lastRosterFingerprint = "", lastStatusFingerprint = "", pendingRosterFingerprint = "", pendingMapValueRefreshReason = "", lastMapValueFingerprint = "";
        private int rosterStableScans, broadEnemyDiscoveryAttempts;
        private bool rosterPublished, enemyRosterDirty, mapValueDirty, pendingMapValueRefresh;
        private int cachedLocalPlayerViewId = int.MinValue;
        private bool gameplayActive;
        private Coroutine pendingGameplayActivation;

        private bool wasCursorVisible = false;
        private bool pendingCursorState = false;
        private float cursorStateChangeTime = 0f;
        private bool wasOverlayHidden = false;
        private float focusLostTime = 0f; // <-- Добавь эту строку

        private ConfigEntry<string> endpoint, levelEndpoint, overlayAppRelativePath, overlayAppArchiveName;
        private ConfigEntry<float> scanInterval, statusInterval;
        private ConfigEntry<bool> requireLineOfSight, preferPlayerVisionDetection, debugLogging, autoStartOverlayApp, autoCloseOverlayApp;
        private Harmony harmony;
        private Process launchedOverlayProcess;

        private void Awake()
        {
            instance = this;
            KeepPluginObjectAlive();
            endpoint = Config.Bind("Overlay", "Endpoint", "http://127.0.0.1:8787/api/monster-seen", "Monster endpoint on this PC.");
            levelEndpoint = Config.Bind("Overlay", "LevelEndpoint", "http://127.0.0.1:8787/api/level", "Level sync endpoint on this PC.");
            scanInterval = Config.Bind("Detection", "ScanIntervalSeconds", 6f, "How often pending enemy roster sync is retried.");
            statusInterval = Config.Bind("Detection", "StatusIntervalSeconds", 15f, "How often monster health/respawn sync is retried.");

            requireLineOfSight = Config.Bind("Detection", "RequireLineOfSight", true, "Reveal monsters only after an encounter.");
            requireLineOfSight.Value = true;
            Config.Save();

            preferPlayerVisionDetection = Config.Bind("Detection", "PreferPlayerVisionDetection", true, "Use player vision detection.");
            debugLogging = Config.Bind("Debug", "Logging", false, "Write periodic bridge debug logs.");
            autoStartOverlayApp = Config.Bind("OverlayApp", "AutoStart", true, "Start the bundled OverlayHUD desktop app.");
            autoCloseOverlayApp = Config.Bind("OverlayApp", "AutoClose", true, "Close the bundled OverlayHUD desktop app.");
            overlayAppRelativePath = Config.Bind("OverlayApp", "ExecutableRelativePath", Path.Combine("OverlayHUD_app", "OverlayHUD.exe"), "Path to executable.");
            overlayAppArchiveName = Config.Bind("OverlayApp", "ArchiveName", "OverlayHUD_app.zip", "Bundled app archive.");

            Logger.LogInfo("OverlayHUD is running. MonsterEndpoint=" + endpoint.Value + ", LevelEndpoint=" + levelEndpoint.Value);
            StartOverlayAppIfNeeded();
            PatchGameUpdates();
        }

        private void StartOverlayAppIfNeeded()
        {
            if (!autoStartOverlayApp.Value) return;
            try
            {
                string exePath = ResolveOverlayAppPath();
                EnsureOverlayAppExtracted(exePath);
                if (string.IsNullOrWhiteSpace(exePath) || !File.Exists(exePath)) { Logger.LogWarning("Bundled OverlayHUD executable not found: " + exePath); return; }
                string processName = Path.GetFileNameWithoutExtension(exePath);
                if (IsProcessAlreadyRunning(processName)) { Logger.LogInfo("OverlayHUD desktop app is already running."); return; }
                launchedOverlayProcess = Process.Start(new ProcessStartInfo { FileName = exePath, WorkingDirectory = Path.GetDirectoryName(exePath), UseShellExecute = true });
                if (launchedOverlayProcess != null) Logger.LogInfo("Started bundled OverlayHUD desktop app: " + exePath);
            }
            catch (Exception error) { Logger.LogWarning("Failed to start bundled OverlayHUD desktop app: " + error.Message); }
        }

        private string ResolveOverlayAppPath()
        {
            string pluginPath = Assembly.GetExecutingAssembly().Location;
            string pluginDir = string.IsNullOrWhiteSpace(pluginPath) ? Paths.PluginPath : Path.GetDirectoryName(pluginPath);
            return Path.GetFullPath(Path.Combine(pluginDir, overlayAppRelativePath.Value));
        }

        private void EnsureOverlayAppExtracted(string exePath)
        {
            if (File.Exists(exePath)) return;
            string pluginDir = string.IsNullOrWhiteSpace(Assembly.GetExecutingAssembly().Location) ? Paths.PluginPath : Path.GetDirectoryName(Assembly.GetExecutingAssembly().Location);
            string archivePath = Path.Combine(pluginDir, overlayAppArchiveName.Value);
            if (!File.Exists(archivePath)) return;
            string targetDir = Path.GetDirectoryName(exePath);
            try
            {
                if (Directory.Exists(targetDir)) Directory.Delete(targetDir, true);
                Directory.CreateDirectory(targetDir);
                ZipFile.ExtractToDirectory(archivePath, targetDir);
            }
            catch { }
        }

        private static bool IsProcessAlreadyRunning(string processName) { try { return Process.GetProcessesByName(processName).Length > 0; } catch { return false; } }

        private void StopOverlayAppIfNeeded()
        {
            if (!autoCloseOverlayApp.Value || launchedOverlayProcess == null) return;
            try
            {
                if (launchedOverlayProcess.HasExited) return;
                if (!launchedOverlayProcess.CloseMainWindow() || !launchedOverlayProcess.WaitForExit(2500))
                {
                    launchedOverlayProcess.Kill();
                    launchedOverlayProcess.WaitForExit(2500);
                }
            }
            catch { }
            finally { launchedOverlayProcess = null; }
        }

        private void PatchGameUpdates()
        {
            try
            {
                harmony = new Harmony("local.overlay.overlay_hud");
                MethodInfo eSpawn = AccessTools.Method("EnemyParent:SpawnRPC");
                MethodInfo eDespawn = AccessTools.Method("EnemyParent:DespawnRPC");
                MethodInfo eDisDec = AccessTools.Method("EnemyParent:DisableDecrease");
                MethodInfo eDesTimer = AccessTools.Method("EnemyParent:DespawnedTimerSet");
                MethodInfo ePlayerClose = AccessTools.Method("EnemyParent:PlayerCloseLogic");
                MethodInfo eOnScreen = AccessTools.Method("EnemyOnScreen:Logic");
                MethodInfo lvlGenStart = AccessTools.Method("LevelGenerator:StartRoomGeneration");
                MethodInfo runLvl = AccessTools.Method("RunManager:ChangeLevel");
                MethodInfo rdExtr = AccessTools.Method("RoundDirector:ExtractionCompleted");
                MethodInfo valSetRpc = AccessTools.Method("ValuableObject:DollarValueSetRPC");
                MethodInfo valSetLog = AccessTools.Method("ValuableObject:DollarValueSetLogic");
                MethodInfo valAdd = AccessTools.Method("ValuableObject:AddToDollarHaulList");
                MethodInfo valAddRpc = AccessTools.Method("ValuableObject:AddToDollarHaulListRPC");
                MethodInfo valRem = AccessTools.Method("ValuableObject:RemoveFromDollarHaulList");
                MethodInfo valRemRpc = AccessTools.Method("ValuableObject:RemoveFromDollarHaulListRPC");
                MethodInfo physBreak = AccessTools.Method("PhysGrabObjectImpactDetector:BreakRPC");
                MethodInfo physDestr = AccessTools.Method("PhysGrabObject:DestroyPhysGrabObjectRPC");
                MethodInfo eVision = AccessTools.Method("EnemyVision:VisionTrigger");
                MethodInfo eHurt = AccessTools.Method("EnemyHealth:Hurt");
                MethodInfo eHurtRpc = AccessTools.Method("EnemyHealth:HurtRPC");

                if (eSpawn != null) harmony.Patch(eSpawn, postfix: new HarmonyMethod(AccessTools.Method(typeof(Plugin), nameof(EnemyParentSpawnedPostfix))));
                if (eDespawn != null) harmony.Patch(eDespawn, postfix: new HarmonyMethod(AccessTools.Method(typeof(Plugin), nameof(EnemyParentDespawnedPostfix))));
                if (eDisDec != null) harmony.Patch(eDisDec, postfix: new HarmonyMethod(AccessTools.Method(typeof(Plugin), nameof(EnemyParentTimerChangedPostfix))));
                if (eDesTimer != null) harmony.Patch(eDesTimer, postfix: new HarmonyMethod(AccessTools.Method(typeof(Plugin), nameof(EnemyParentTimerChangedPostfix))));
                if (ePlayerClose != null) harmony.Patch(ePlayerClose, postfix: new HarmonyMethod(AccessTools.Method(typeof(Plugin), nameof(EnemyParentPlayerCloseLogicPostfix))));
                if (eOnScreen != null) harmony.Patch(eOnScreen, postfix: new HarmonyMethod(AccessTools.Method(typeof(Plugin), nameof(EnemyOnScreenLogicPostfix))));
                if (lvlGenStart != null) harmony.Patch(lvlGenStart, prefix: new HarmonyMethod(AccessTools.Method(typeof(Plugin), nameof(LevelGenerationStartingPrefix))));
                if (runLvl != null) harmony.Patch(runLvl, prefix: new HarmonyMethod(AccessTools.Method(typeof(Plugin), nameof(LevelChangingPrefix))), postfix: new HarmonyMethod(AccessTools.Method(typeof(Plugin), nameof(LevelChangedPostfix))));
                if (rdExtr != null) harmony.Patch(rdExtr, postfix: new HarmonyMethod(AccessTools.Method(typeof(Plugin), nameof(ExtractionCompletedPostfix))));
                if (valSetRpc != null) harmony.Patch(valSetRpc, postfix: new HarmonyMethod(AccessTools.Method(typeof(Plugin), nameof(ValuableDollarValueSetRpcPostfix))));
                if (valSetLog != null) harmony.Patch(valSetLog, postfix: new HarmonyMethod(AccessTools.Method(typeof(Plugin), nameof(ValuableDollarValueSetLogicPostfix))));
                if (valAdd != null) harmony.Patch(valAdd, postfix: new HarmonyMethod(AccessTools.Method(typeof(Plugin), nameof(ValuableDollarHaulAddPostfix))));
                if (valAddRpc != null) harmony.Patch(valAddRpc, postfix: new HarmonyMethod(AccessTools.Method(typeof(Plugin), nameof(ValuableDollarHaulAddPostfix))));
                if (valRem != null) harmony.Patch(valRem, postfix: new HarmonyMethod(AccessTools.Method(typeof(Plugin), nameof(ValuableDollarHaulRemovePostfix))));
                if (valRemRpc != null) harmony.Patch(valRemRpc, postfix: new HarmonyMethod(AccessTools.Method(typeof(Plugin), nameof(ValuableDollarHaulRemovePostfix))));
                if (physBreak != null) harmony.Patch(physBreak, postfix: new HarmonyMethod(AccessTools.Method(typeof(Plugin), nameof(PhysGrabObjectBreakPostfix))));
                if (physDestr != null) harmony.Patch(physDestr, postfix: new HarmonyMethod(AccessTools.Method(typeof(Plugin), nameof(PhysGrabObjectDestroyedPostfix))));
                if (eVision != null) harmony.Patch(eVision, postfix: new HarmonyMethod(AccessTools.Method(typeof(Plugin), nameof(EnemyVisionTriggerPostfix))));

                if (eHurt != null) harmony.Patch(eHurt, postfix: new HarmonyMethod(AccessTools.Method(typeof(Plugin), nameof(EnemyHealthChangedPostfix))));
                if (eHurtRpc != null) harmony.Patch(eHurtRpc, postfix: new HarmonyMethod(AccessTools.Method(typeof(Plugin), nameof(EnemyHealthHurtRpcPostfix))));

                foreach (string methodName in UpgradeStateKeyByPunMethod.Keys)
                {
                    MethodInfo upgMethod = AccessTools.Method("PunManager:" + methodName);
                    if (upgMethod != null) harmony.Patch(upgMethod, postfix: new HarmonyMethod(AccessTools.Method(typeof(Plugin), nameof(PlayerUpgradeAppliedPostfix))));
                }
            }
            catch (Exception ex) { Logger.LogWarning("Failed to patch game: " + ex.Message); }
            SceneManager.sceneLoaded += OnSceneLoaded;
        }

        private void KeepPluginObjectAlive()
        {
            try
            {
                if (gameObject.transform.parent != null) gameObject.transform.parent = null;
                gameObject.hideFlags = HideFlags.HideAndDontSave;
                DontDestroyOnLoad(gameObject);
            }
            catch { }
        }

        private void Update()
        {
            if (!gameplayActive)
            {
                if (pendingGameplayActivation == null && CachedIsRunLevel(SceneManager.GetActiveScene().name))
                {
                    ScheduleGameplayActivation("Client update fallback");
                }
                return;
            }

            // --- НОВЫЙ КОД: Умное скрытие оверлея ---
            if (Application.isFocused)
            {
                focusLostTime = 0f;
                if (wasOverlayHidden)
                {
                    wasOverlayHidden = false;
                    if (gameObject.activeInHierarchy) StartCoroutine(PostTabHidden(false));
                }
            }
            else
            {
                focusLostTime += Time.unscaledDeltaTime;
                // Ждем 0.5 секунды. Уведомления Windows крадут фокус лишь на мгновение.
                if (focusLostTime > 0.5f && !wasOverlayHidden)
                {
                    wasOverlayHidden = true;
                    if (gameObject.activeInHierarchy) StartCoroutine(PostTabHidden(true));
                }
            }
            // ----------------------------------------

            bool isCursorVisible = Cursor.visible;
            if (isCursorVisible != pendingCursorState)
            {
                pendingCursorState = isCursorVisible;
                cursorStateChangeTime = Time.unscaledTime + 0.3f;
            }
            if (pendingCursorState != wasCursorVisible && Time.unscaledTime >= cursorStateChangeTime)
            {
                wasCursorVisible = pendingCursorState;
                if (gameObject.activeInHierarchy) StartCoroutine(PostCursorState(wasCursorVisible));
            }

            if (!CachedIsMasterClient())
            {
                var keys = new List<int>(clientSimulatedTimers.Keys);
                foreach (int k in keys)
                {
                    if (clientSimulatedTimers[k] > 0f)
                    {
                        clientSimulatedTimers[k] -= Time.deltaTime;
                        if (clientSimulatedTimers[k] <= 0f) clientSimulatedTimers[k] = 0f;
                    }
                }
            }

            TickScan();
        }

        private static void LevelGenerationStartingPrefix() { instance?.ResetMapValue("room generation started"); }
        private static void LevelChangingPrefix() { instance?.HandleLevelChanging(); }
        private static void LevelChangedPostfix(object __instance) { instance?.ScheduleGameplayActivation("RunManager.ChangeLevel"); }

        private static void PlayerUpgradeAppliedPostfix(MethodBase __originalMethod, string _steamID, int __result)
        {
            string methodName = __originalMethod?.Name;
            if (methodName != null && UpgradeStateKeyByPunMethod.TryGetValue(methodName, out string stateKey))
            {
                instance?.SyncPlayerUpgradeValue(stateKey, _steamID, __result);
            }
        }

        private void SyncPlayerUpgradeValue(string stateKey, string steamId, int value)
        {
            if (!gameplayActive || string.IsNullOrEmpty(stateKey) || string.IsNullOrEmpty(steamId)) return;
            SyncPlayerUpgradesIfChanged(null);
        }

        private static void EnemyParentSpawnedPostfix(object __instance)
        {
            if (__instance is Component component)
            {
                RegisterEnemyParent(component);
                if (instance != null)
                {
                    GameObject root = GetEnemyRoot(component);
                    if (root != null) instance.clientSimulatedHealth.Remove(root.GetInstanceID());
                }
                instance?.SyncEnemyParentStatusChanged(component);
            }
        }

        private static void EnemyParentDespawnedPostfix(object __instance)
        {
            if (__instance is Component component) instance?.ScheduleEnemyParentStatusChanged(component);
        }

        private static void EnemyParentTimerChangedPostfix(object __instance)
        {
            if (__instance is Component component) instance?.SyncEnemyParentTimerChanged(component);
        }

        private static void EnemyParentPlayerCloseLogicPostfix(object __instance, ref IEnumerator __result)
        {
            if (__result != null && __instance is Component enemyParent) __result = WatchBlindEnemyPlayerClose(__result, enemyParent);
        }

        private static void EnemyOnScreenLogicPostfix(object __instance, ref IEnumerator __result)
        {
            if (__result != null && __instance is Component enemyOnScreen) __result = WatchEnemyOnScreen(__result, enemyOnScreen);
        }

        private static void ExtractionCompletedPostfix() { instance?.RefreshMapValue("extraction completed"); }
        private static void ValuableDollarValueSetRpcPostfix(object __instance, float value) { instance?.ScheduleMapValueRefresh("valuable rpc"); }
        private static void ValuableDollarValueSetLogicPostfix(object __instance) { if (CachedIsMasterClient()) instance?.ScheduleMapValueRefresh("valuable logic"); }
        private static void ValuableDollarHaulAddPostfix(object __instance) { TrackDollarHaulValuable(__instance, true); }
        private static void ValuableDollarHaulRemovePostfix(object __instance) { TrackDollarHaulValuable(__instance, false); }

        private static void PhysGrabObjectBreakPostfix(object __instance, float valueLost, bool _loseValue)
        {
            if (!_loseValue) return;
            instance?.AddMapValue(-valueLost, "valuable break");
            instance?.AddLostValue(valueLost, "valuable break");
        }

        private static void PhysGrabObjectDestroyedPostfix(object __instance)
        {
            if (!CachedIsRunLevel(null)) return;
            Component valuable = GetValuableComponent(__instance);
            if (valuable == null) return;
            float current = ReadValuableCurrentValue(valuable), orig = ReadValuableOriginalValue(valuable);
            if (orig > 0f && current < orig * 0.15f) return;
            instance?.AddMapValue(-current, "valuable destroyed");
            if (!IsValuableInDollarHaul(valuable)) instance?.AddLostValue(current, "valuable destroyed");
        }

        private static void EnemyVisionTriggerPostfix(object __instance, int playerID, object player, bool culled, bool playerNear)
        {
            instance?.HandleEnemyVisionTrigger(__instance, playerID);
        }

        private static void EnemyHealthChangedPostfix(object __instance) { instance?.SyncEnemyHealthChanged(__instance); }

        private static void EnemyHealthHurtRpcPostfix(object __instance, object[] __args)
        {
            if (instance == null || !instance.gameplayActive || __instance == null || __args == null || __args.Length == 0) return;

            float damage = 0f;
            if (__args[0] != null) TryConvertFloat(__args[0], out damage);

            Component enemy = ReadMember(__instance, "enemy") as Component;
            Component enemyParent = ReadMember(enemy ?? __instance, "EnemyParent") as Component;

            if (enemyParent != null && damage > 0f)
            {
                GameObject root = GetEnemyRoot(enemyParent);
                if (root != null)
                {
                    int id = root.GetInstanceID();
                    var cand = new EnemyCandidate { Component = enemyParent, Root = root, Center = Vector3.zero };

                    if (!instance.clientSimulatedHealth.ContainsKey(id))
                    {
                        if (instance.TryGetEnemyHealth(cand, out float h, out float mh)) instance.clientSimulatedHealth[id] = h;
                    }

                    if (instance.clientSimulatedHealth.ContainsKey(id))
                    {
                        instance.clientSimulatedHealth[id] -= damage;
                        if (instance.clientSimulatedHealth[id] < 0f) instance.clientSimulatedHealth[id] = 0f;
                    }
                }
                instance.SyncEnemyParentStatusChanged(enemyParent);
            }
        }

        private void TickScan()
        {
            if (!gameplayActive) return;
            float now = Time.realtimeSinceStartup;
            if (mapValueDirty && now >= nextMapValueSyncAt) SyncMapValueIfChanged();
            if (now < scanPausedUntil) return;
            if (pendingUpgradeKeys.Count > 0 && now >= nextUpgradeSyncAt)
            {
                var keys = new HashSet<string>(pendingUpgradeKeys);
                pendingUpgradeKeys.Clear();
                SyncPlayerUpgradesIfChanged(keys);
            }
            if (rosterPublished && now >= nextStatusSyncAt)
            {
                nextStatusSyncAt = now + Math.Max(10f, statusInterval.Value);
                SyncMonsterStatuses(new List<ResolvedEnemyCandidate>());
            }
            if (!enemyRosterDirty || now < nextScanAt) return;
            nextScanAt = now + Math.Max(0.05f, scanInterval.Value);
            try { SyncKnownEnemies(); } catch { }
        }

        private void OnDestroy()
        {
            SceneManager.sceneLoaded -= OnSceneLoaded;
            harmony?.UnpatchSelf();
            if (gameplayActive) HandleLevelChanging();
            StopOverlayAppIfNeeded();
            if (instance == this) instance = null;
        }

        private void OnSceneLoaded(Scene scene, LoadSceneMode mode)
        {
            if (gameplayActive && !CachedIsRunLevel(scene.name))
                HandleLevelChanging();
            else if (!gameplayActive && CachedIsRunLevel(scene.name))
                ScheduleGameplayActivation("Scene loaded");
        }

        private void ScheduleGameplayActivation(string reason)
        {
            if (pendingGameplayActivation != null) StopCoroutine(pendingGameplayActivation);
            if (gameObject.activeInHierarchy) pendingGameplayActivation = StartCoroutine(ActivateGameplayAfterLevelChange(reason));
        }

        private IEnumerator ActivateGameplayAfterLevelChange(string reason)
        {
            for (int attempt = 1; attempt <= 40; attempt++)
            {
                yield return new WaitForSecondsRealtime(0.25f);
                if (IsGameplayLevelCandidate(out _))
                {
                    yield return new WaitForSecondsRealtime(5f);
                    HandleGameplayDetected(reason);
                    pendingGameplayActivation = null;
                    yield break;
                }
                if (IsNonGameplayContext() && attempt > 5) break;
            }
            pendingGameplayActivation = null;
        }

        private bool HandleGameplayDetected(string reason)
        {
            if (gameplayActive) return true;

            ResetSeenMonsters("new level generated");
            mapValue = 0f; mapValueInitial = 0f; lostValue = 0f; valuablesInDollarHaul.Clear();
            lastMapValueFingerprint = ""; mapValueInitial = mapValue; gameplayActive = true;

            int level = ResolveCurrentLevel();
            if (level > 0) SyncLevelToOverlay(level, ResolveCurrentLevelName());
            return true;
        }

        private void HandleLevelChanging()
        {
            if (!gameplayActive) return;
            gameplayActive = false;
            SyncMapValueIfChanged();
            ResetMapValue("level changing");
            if (gameObject.activeInHierarchy) StartCoroutine(PostVisibility(false));
        }

        private void ResetMapValue(string reason)
        {
            mapValue = 0f; mapValueInitial = 0f; lostValue = 0f; valuablesInDollarHaul.Clear();
            lastMapValueFingerprint = ""; mapValueDirty = false; pendingMapValueRefresh = false; pendingMapValueRefreshReason = "";
        }

        private void RefreshMapValue(string reason) { if (CachedIsRunLevel(null)) { mapValue = CalculateMapValue(); MarkMapValueDirty(); } }
        private void ScheduleMapValueRefresh(string reason) { if (CachedIsRunLevel(null)) { pendingMapValueRefresh = true; pendingMapValueRefreshReason = reason; MarkMapValueDirty(); } }
        private void AddMapValue(float delta, string reason) { if (CachedIsRunLevel(null) && !float.IsNaN(delta) && Math.Abs(delta) >= 0.01f) { mapValue = Math.Max(0f, mapValue + delta); MarkMapValueDirty(); } }
        private void AddLostValue(float value, string reason) { if (CachedIsRunLevel(null) && !float.IsNaN(value) && value >= 0.01f) { lostValue += value; MarkMapValueDirty(); } }

        // ОПТИМИЗАЦИЯ: Увеличиваем задержку отправки стоимости лута, чтобы не лагало при смерти и лутании
        private void MarkMapValueDirty() { mapValueDirty = true; nextMapValueSyncAt = Time.realtimeSinceStartup + 1.0f; }

        private void SyncMapValueIfChanged()
        {
            mapValueDirty = false;
            if (pendingMapValueRefresh) { pendingMapValueRefresh = false; mapValue = CalculateMapValue(); if (mapValueInitial <= 0f && mapValue > 0f) mapValueInitial = mapValue; pendingMapValueRefreshReason = ""; }
            int val = Math.Max(0, (int)Math.Round(mapValue)), init = Math.Max(0, (int)Math.Round(mapValueInitial)), lost = Math.Max(0, (int)Math.Round(lostValue));
            int? goal = ResolveExtractionGoal();
            string fp = val + ":" + init + ":" + lost + ":" + (goal.HasValue ? goal.Value.ToString() : "");
            if (fp == lastMapValueFingerprint) return;
            lastMapValueFingerprint = fp;
            if (gameObject.activeInHierarchy) StartCoroutine(PostMapValue(val, init, lost, goal));
        }

        private void ResetSeenMonsters(string reason)
        {
            lock (seenLock) { seenMonsters.Clear(); }
            lock (enemyLock) { knownEnemyParents.Clear(); sentEnemyInstanceIds.Clear(); }
            lastSeenLoggedAt.Clear(); resolvedMonsterNames.Clear(); sourceIdsByEnemyParent.Clear();
            lastAliveBySourceId.Clear(); lastHealthDebugBySourceId.Clear(); healthSourcesByRootId.Clear();
            lastImmediateStatusBySourceId.Clear(); lastTimerStatusBySourceId.Clear(); lastTimerStatusSentAtBySourceId.Clear();
            enemyHasVisionByParentId.Clear(); enemyHasOnScreenByParentId.Clear(); visionEnemyCacheByVisionId.Clear();
            pendingEncounterIds.Clear(); cachedLocalPlayerViewId = int.MinValue;
            lastRosterFingerprint = ""; lastStatusFingerprint = ""; pendingRosterFingerprint = "";
            rosterStableScans = 0; broadEnemyDiscoveryAttempts = 0; rosterPublished = false; enemyRosterDirty = true;
            scanPausedUntil = Time.realtimeSinceStartup + 2f; nextScanAt = scanPausedUntil; nextStatusSyncAt = scanPausedUntil;
            nextUpgradeSyncAt = scanPausedUntil; nextBroadEnemyDiscoveryAt = scanPausedUntil;
            nextStatusDirectorRecoveryAt = scanPausedUntil;
            clientSimulatedTimers.Clear(); clientSimulatedHealth.Clear();
        }

        private void SyncKnownEnemies()
        {
            List<EnemyCandidate> found = FindEnemyCandidates();
            var resolvedEnemies = new List<ResolvedEnemyCandidate>();
            foreach (EnemyCandidate cand in found)
            {
                int iId = cand.Root.GetInstanceID();
                if (!resolvedMonsterNames.TryGetValue(iId, out string mName)) { mName = ResolveMonsterName(cand.Component); if (mName != null) resolvedMonsterNames[iId] = mName; }
                if (mName != null) resolvedEnemies.Add(new ResolvedEnemyCandidate { Candidate = cand, MonsterName = mName });
            }

            if (!SyncMonsterRoster(resolvedEnemies)) return;
            if (!requireLineOfSight.Value) RevealAllKnownEnemies(resolvedEnemies);

            if (resolvedEnemies.Count == 0) { enemyRosterDirty = false; return; }
            SyncMonsterStatuses(resolvedEnemies);
            TryPublishPendingVisionEncounters(resolvedEnemies);
            enemyRosterDirty = false;
        }

        private void RevealAllKnownEnemies(List<ResolvedEnemyCandidate> enemies)
        {
            foreach (var res in enemies)
            {
                int iId = res.Candidate.Root.GetInstanceID();
                if (!TryMarkEnemySent(iId)) continue;
                pendingEncounterIds.Remove(iId);
                MarkMonsterSeen(res.MonsterName, res.Candidate);
                if (gameObject.activeInHierarchy) StartCoroutine(PostSeenMonster(res.MonsterName, iId));
            }
        }

        private bool SyncMonsterRoster(List<ResolvedEnemyCandidate> enemies)
        {
            enemies.Sort((l, r) => l.Candidate.Root.GetInstanceID().CompareTo(r.Candidate.Root.GetInstanceID()));
            var fp = new StringBuilder();
            foreach (var e in enemies) fp.Append(e.Candidate.Root.GetInstanceID()).Append(':').Append(e.MonsterName).Append(';');
            string nextFp = fp.ToString();

            if (!rosterPublished)
            {
                if (nextFp != pendingRosterFingerprint) { pendingRosterFingerprint = nextFp; rosterStableScans = 0; return false; }
                if (++rosterStableScans < 2) return false;
                rosterPublished = true;
            }

            if (nextFp == lastRosterFingerprint) return true;
            lastRosterFingerprint = nextFp;
            var json = new StringBuilder("{\"monsters\":[");
            for (int i = 0; i < enemies.Count; i++)
            {
                if (i > 0) json.Append(',');
                json.Append("{\"id\":").Append(enemies[i].Candidate.Root.GetInstanceID()).Append(",\"name\":\"").Append(EscapeJson(enemies[i].MonsterName)).Append("\"}");
            }
            json.Append("]}");
            if (gameObject.activeInHierarchy) StartCoroutine(PostMonsterRoster(json.ToString()));
            return true;
        }

        private void SyncMonsterStatuses(List<ResolvedEnemyCandidate> enemies)
        {
            var json = new StringBuilder("{\"statuses\":[");
            var fp = new StringBuilder();
            int statusCount = 0;
            var cands = new Dictionary<int, EnemyCandidate>();
            foreach (var e in enemies)
            {
                int sId = e.Candidate.Root.GetInstanceID();
                cands[sId] = e.Candidate;
                Component p = GetEnemyParent(e.Candidate);
                if (p != null) sourceIdsByEnemyParent[p.GetInstanceID()] = sId;
            }
            foreach (Component p in GetKnownEnemyParentsSnapshot()) if (p != null) AddStatusCandidate(cands, p);
            float now = Time.realtimeSinceStartup;
            if (cands.Count == 0 || now >= nextStatusDirectorRecoveryAt)
            {
                nextStatusDirectorRecoveryAt = now + 30f;
                foreach (Component p in FindSpawnedEnemiesFromDirector()) if (p != null) { RegisterEnemyParent(p); AddStatusCandidate(cands, p); }
            }
            var keys = new List<int>(cands.Keys); keys.Sort();
            foreach (int iId in keys)
            {
                EnemyCandidate cand = cands[iId];
                if (!TryGetEnemyRespawnStatus(cand, out bool alive, out float rem)) continue;

                float h = 0f, mh = 0f;
                bool ih = IsEnemySent(iId);
                bool hasHealth = ih && TryGetEnemyHealth(cand, out h, out mh);

                Component sep = GetEnemyParent(cand);
                bool pc = IsEnemyParentPlayerClose(sep), pvc = IsEnemyParentPlayerVeryClose(sep);
                lastAliveBySourceId[iId] = alive;
                float rr = alive ? 0f : (float)Math.Ceiling(Math.Max(0f, rem) * 10f) / 10f;
                string rt = rr.ToString("0.0", CultureInfo.InvariantCulture), ht = hasHealth ? Math.Max(0f, h).ToString("0.#", CultureInfo.InvariantCulture) : "", mht = hasHealth && mh > 0f ? mh.ToString("0.#", CultureInfo.InvariantCulture) : "";
                fp.Append(iId).Append(':').Append(alive ? '1' : '0').Append(':').Append(rt).Append(':').Append(ht).Append('/').Append(mht).Append(':').Append(pc ? '1' : '0').Append(':').Append(pvc ? '1' : '0').Append(';');
                if (statusCount++ > 0) json.Append(',');
                json.Append("{\"id\":").Append(iId).Append(",\"alive\":").Append(alive ? "true" : "false").Append(",\"respawnRemaining\":").Append(rt).Append(",\"playerClose\":").Append(pc ? "true" : "false").Append(",\"playerVeryClose\":").Append(pvc ? "true" : "false");
                if (hasHealth) { json.Append(",\"health\":").Append(ht.Length > 0 ? ht : "0"); if (mht.Length > 0) json.Append(",\"maxHealth\":").Append(mht); }
                json.Append('}');
            }
            if (statusCount == 0) return;
            string nFp = fp.ToString();
            if (nFp == lastStatusFingerprint) return;
            lastStatusFingerprint = nFp; json.Append("]}");
            if (gameObject.activeInHierarchy) StartCoroutine(PostMonsterStatuses(json.ToString(), true));
        }

        private static bool TryGetEnemyRespawnStatus(EnemyCandidate candidate, out bool alive, out float remaining)
        {
            alive = true; remaining = 0f;
            Component p = GetEnemyParent(candidate);
            if (p == null) return false;

            alive = ReadEnemySpawned(p);
            TryConvertFloat(ReadMember(p, "DespawnedTimer"), out float realTimer);

            if (instance != null && candidate.Root != null)
            {
                int id = candidate.Root.GetInstanceID();
                if (!alive)
                {
                    if (CachedIsMasterClient())
                    {
                        // У хоста таймер всегда правильный
                        remaining = realTimer;
                        instance.clientSimulatedTimers[id] = remaining;
                    }
                    else
                    {
                        // У клиента: если пришла новая цифра по сети (отличается от нашей симуляции), обновляем
                        if (!instance.clientSimulatedTimers.TryGetValue(id, out float sim) || (realTimer > 0f && Math.Abs(realTimer - sim) > 1.5f))
                        {
                            instance.clientSimulatedTimers[id] = realTimer;
                        }

                        remaining = instance.clientSimulatedTimers[id];
                    }
                }
                else
                {
                    instance.clientSimulatedTimers[id] = 0f;
                }
            }
            return true;
        }

        private void AddStatusCandidate(Dictionary<int, EnemyCandidate> statusCandidates, Component enemyParent)
        {
            GameObject root = GetEnemyRoot(enemyParent);
            int pId = enemyParent.GetInstanceID(), sId;
            if (root != null) { sId = root.GetInstanceID(); sourceIdsByEnemyParent[pId] = sId; }
            else if (!sourceIdsByEnemyParent.TryGetValue(pId, out sId)) return;
            statusCandidates[sId] = new EnemyCandidate { Component = enemyParent, Root = root, Center = Vector3.zero };
        }

        private void SyncEnemyHealthChanged(object enemyHealthSource)
        {
            if (!gameplayActive || enemyHealthSource == null) return;
            Component enemyParent = ReadMember(ReadMember(enemyHealthSource, "enemy") as Component, "EnemyParent") as Component;
            SyncEnemyParentStatusChanged(enemyParent);
        }

        private void ScheduleEnemyParentStatusChanged(Component enemyParent)
        {
            if (gameplayActive && enemyParent != null && gameObject.activeInHierarchy) StartCoroutine(SyncEnemyParentStatusChangedNextFrame(enemyParent));
        }

        private IEnumerator SyncEnemyParentStatusChangedNextFrame(Component enemyParent)
        {
            for (int i = 0; i < 6; i++) { yield return new WaitForSecondsRealtime(0.2f); SyncEnemyParentStatusChanged(enemyParent); }
        }

        private void SyncEnemyParentTimerChanged(Component enemyParent)
        {
            if (!gameplayActive || enemyParent == null) return;
            GameObject root = GetEnemyRoot(enemyParent);
            if (root == null || !IsEnemySent(root.GetInstanceID())) return;
            var c = new EnemyCandidate { Component = enemyParent, Root = root, Center = Vector3.zero };
            if (!TryGetEnemyRespawnStatus(c, out bool a, out float r)) return;
            int iId = root.GetInstanceID(); float rr = a ? 0f : (float)Math.Ceiling(Math.Max(0f, r) * 10f) / 10f;
            string rt = rr.ToString("0.0", CultureInfo.InvariantCulture), fp = iId + ":" + (a ? "1" : "0") + ":" + rt;
            bool ac = !lastAliveBySourceId.TryGetValue(iId, out bool pa) || pa != a;
            if (!ac && lastTimerStatusBySourceId.TryGetValue(iId, out string pf) && pf == fp) return;
            float now = Time.realtimeSinceStartup;
            if (!ac && lastTimerStatusSentAtBySourceId.TryGetValue(iId, out float lsa) && now - lsa < 0.5f) return;
            lastAliveBySourceId[iId] = a; lastTimerStatusBySourceId[iId] = fp; lastTimerStatusSentAtBySourceId[iId] = now;
            if (gameObject.activeInHierarchy) StartCoroutine(PostMonsterStatuses("{\"statuses\":[{\"id\":" + iId + ",\"alive\":" + (a ? "true" : "false") + ",\"respawnRemaining\":" + rt + "}]}"));
        }

        private void SyncEnemyParentStatusChanged(Component enemyParent)
        {
            if (!gameplayActive || enemyParent == null) return;
            GameObject root = GetEnemyRoot(enemyParent);
            if (root == null) return;
            int iId = root.GetInstanceID();
            var c = new EnemyCandidate { Component = enemyParent, Root = root, Center = Vector3.zero };
            if (!TryGetEnemyRespawnStatus(c, out bool a, out float r)) return;

            bool ih = IsEnemySent(iId);
            float h = 0f, mh = 0f;
            bool hh = ih && TryGetEnemyHealth(c, out h, out mh);

            bool pc = IsEnemyParentPlayerClose(enemyParent), pvc = IsEnemyParentPlayerVeryClose(enemyParent);
            float rr = a ? 0f : (float)Math.Ceiling(Math.Max(0f, r) * 10f) / 10f;
            string rt = rr.ToString("0.0", CultureInfo.InvariantCulture), ht = hh ? Math.Max(0f, h).ToString("0.#", CultureInfo.InvariantCulture) : "", mht = hh && mh > 0f ? mh.ToString("0.#", CultureInfo.InvariantCulture) : "";
            string fp = iId + ":" + (a ? "1" : "0") + ":" + rt + ":" + ht + "/" + mht + ":" + (pc ? "1" : "0") + ":" + (pvc ? "1" : "0");
            if (lastImmediateStatusBySourceId.TryGetValue(iId, out string pf) && pf == fp) return;
            lastImmediateStatusBySourceId[iId] = fp;
            var json = new StringBuilder("{\"statuses\":[{\"id\":").Append(iId).Append(",\"alive\":").Append(a ? "true" : "false").Append(",\"respawnRemaining\":").Append(rt).Append(",\"playerClose\":").Append(pc ? "true" : "false").Append(",\"playerVeryClose\":").Append(pvc ? "true" : "false");
            if (hh) { json.Append(",\"health\":").Append(ht.Length > 0 ? ht : "0"); if (mht.Length > 0) json.Append(",\"maxHealth\":").Append(mht); }
            json.Append("}]}");
            if (gameObject.activeInHierarchy) StartCoroutine(PostMonsterStatuses(json.ToString()));
        }

        private static bool ReadEnemySpawned(Component enemyParent)
        {
            object sv = ReadMember(enemyParent, "Spawned");
            return sv is bool b ? b : (enemyParent.gameObject != null && enemyParent.gameObject.activeInHierarchy);
        }

        private bool TryGetEnemyHealth(EnemyCandidate candidate, out float health, out float maxHealth)
        {
            health = 0f; maxHealth = 0f; bool hasHealth = false;
            foreach (object source in GetEnemyHealthSources(candidate))
            {
                if (source == null) continue;
                if (!hasHealth && TryReadFirstFloat(source, CurrentHealthMemberNames, out float cv)) { health = Math.Max(0f, cv); hasHealth = true; }
                if (maxHealth <= 0f && TryReadFirstFloat(source, MaxHealthMemberNames, out float mv)) maxHealth = Math.Max(0f, mv);
                if (hasHealth && maxHealth > 0f) break;
            }

            if (candidate.Root != null)
            {
                int id = candidate.Root.GetInstanceID();
                if (clientSimulatedHealth.TryGetValue(id, out float simH))
                {
                    if (hasHealth && health < simH)
                    {
                        clientSimulatedHealth[id] = health;
                    }
                    else
                    {
                        health = simH;
                        hasHealth = true;
                    }
                }
            }

            if (!hasHealth && maxHealth > 0f) { health = maxHealth; return true; }
            return hasHealth;
        }

        private IEnumerable<object> GetEnemyHealthSources(EnemyCandidate candidate)
        {
            if (candidate.Root != null)
            {
                int rootId = candidate.Root.GetInstanceID();
                if (!healthSourcesByRootId.TryGetValue(rootId, out object[] cachedSources))
                {
                    var sources = new List<object>();
                    Component enemy = candidate.Root.GetComponent("Enemy");
                    object linkedHealth = ReadMember(enemy, "Health");
                    if (linkedHealth != null) sources.Add(linkedHealth);
                    Component enemyHealth = candidate.Root.GetComponent("EnemyHealth");
                    if (enemyHealth != null && !sources.Contains(enemyHealth)) sources.Add(enemyHealth);
                    if (enemy != null && !sources.Contains(enemy)) sources.Add(enemy);
                    cachedSources = sources.ToArray(); healthSourcesByRootId[rootId] = cachedSources;
                }
                foreach (var source in cachedSources) if (!(source is UnityEngine.Object obj && obj == null)) yield return source;
            }
            if (candidate.Component != null) yield return candidate.Component;
            Component enemyParent = GetEnemyParent(candidate);
            if (enemyParent != null) yield return enemyParent;
        }

        private static bool TryReadFirstFloat(object source, string[] memberNames, out float value)
        {
            foreach (string name in memberNames)
            {
                object raw = ReadMember(source, name);
                if (raw != null && TryConvertFloat(raw, out value)) return true;
            }
            value = 0f; return false;
        }

        private static Component GetEnemyParent(EnemyCandidate candidate)
        {
            if (candidate.Component != null && candidate.Component.GetType().Name == "EnemyParent") return candidate.Component;
            Component enemy = candidate.Root == null ? null : candidate.Root.GetComponent("Enemy");
            return ReadMember(enemy ?? candidate.Component, "EnemyParent") as Component;
        }

        private static bool TryConvertFloat(object value, out float result)
        {
            try { result = Convert.ToSingle(value, CultureInfo.InvariantCulture); return true; } catch { result = 0f; return false; }
        }

        private static bool TryMarkEnemySent(int instanceId) { lock (enemyLock) { return sentEnemyInstanceIds.Add(instanceId); } }
        private static bool IsEnemySent(int instanceId) { lock (enemyLock) { return sentEnemyInstanceIds.Contains(instanceId); } }

        private void MarkMonsterSeen(string monsterName, EnemyCandidate candidate)
        {
            bool added = false;
            lock (seenLock) { if (!seenMonsters.Contains(monsterName)) { seenMonsters.Add(monsterName); added = true; } }
            if (added || ShouldLogSeen(monsterName))
            {
                lastSeenLoggedAt[monsterName] = Time.realtimeSinceStartup;
            }
        }

        private bool ShouldLogSeen(string monsterName)
        {
            if (!debugLogging.Value) return false;
            if (!lastSeenLoggedAt.TryGetValue(monsterName, out float last)) return true;
            return Time.realtimeSinceStartup - last >= 30f;
        }

        private int ResolveCurrentLevel()
        {
            Type runManagerType = AccessTools.TypeByName("RunManager");
            object runManager = ReadMember(runManagerType, "instance");
            object levelsCompleted = ReadMember(runManager, "levelsCompleted");
            if (levelsCompleted != null)
            {
                try { int level = Math.Max(1, Convert.ToInt32(levelsCompleted) + 1); fallbackLevel = level; return level; } catch { }
            }
            fallbackLevel = Math.Max(1, lastSyncedLevel + 1);
            return fallbackLevel;
        }

        private static bool IsRegularGameplayLevel()
        {
            Type runManagerType = AccessTools.TypeByName("RunManager");
            object runManager = ReadMember(runManagerType, "instance");
            object currentLevel = ReadMember(runManager, "levelCurrent");
            object levelsValue = ReadMember(runManager, "levels");
            if (currentLevel != null && levelsValue is IList levels && levels.Contains(currentLevel)) return true;
            if (IsNamedRunLevel(currentLevel)) return true;
            return CachedIsRunLevel(null);
        }

        private static bool IsGameplayLevelCandidate(out string details, bool allowExpensiveFallback = false)
        {
            Type runManagerType = AccessTools.TypeByName("RunManager");
            object runManager = ReadMember(runManagerType, "instance");
            object currentLevel = ReadMember(runManager, "levelCurrent");
            object levelsValue = ReadMember(runManager, "levels");
            string currentLevelName = DescribeLevelObject(currentLevel);
            bool nonGameplayCurrent = IsNonGameplayLevelName(currentLevelName);
            bool listedLevel = !nonGameplayCurrent && currentLevel != null && levelsValue is IList levels && levels.Contains(currentLevel);
            bool namedLevel = IsNamedRunLevel(currentLevel);
            bool runLevel = !nonGameplayCurrent && CachedIsRunLevel(null);
            bool hasLevelGenerator = false;

            bool levelGenerated = IsLevelGenerated() || !CachedIsMasterClient();

            string activeSceneName = SceneManager.GetActiveScene().name;
            bool nonGameplayScene = IsNonGameplayLevelName(activeSceneName);
            string activeNamedLevelObject = "";
            if (nonGameplayCurrent || nonGameplayScene) levelGenerated = false;
            else if (allowExpensiveFallback) { hasLevelGenerator = HasActiveLevelGenerator(); activeNamedLevelObject = FindActiveNamedRunLevelObject(); }
            details = "current=" + currentLevelName + ", generated=" + levelGenerated;
            if (nonGameplayCurrent || nonGameplayScene) return false;
            return levelGenerated && (listedLevel || namedLevel || runLevel || hasLevelGenerator || IsRunLevelName(activeSceneName) || !string.IsNullOrWhiteSpace(activeNamedLevelObject));
        }

        private static bool HasActiveLevelGenerator()
        {
            Type levelGeneratorType = AccessTools.TypeByName("LevelGenerator");
            if (levelGeneratorType == null) return false;
            UnityEngine.Object[] generators = Resources.FindObjectsOfTypeAll(levelGeneratorType);
            foreach (var generator in generators) if (generator is Component component && component.gameObject != null && component.gameObject.scene.IsValid()) return true;
            return false;
        }

        private static bool IsLevelGenerated()
        {
            Type levelGeneratorType = AccessTools.TypeByName("LevelGenerator");
            object levelGenerator = ReadMember(levelGeneratorType, "Instance") ?? ReadMember(levelGeneratorType, "instance");
            object generated = ReadMember(levelGenerator, "Generated");
            return generated is bool value && value;
        }

        private static string FindActiveNamedRunLevelObject()
        {
            UnityEngine.Object[] gameObjects = Resources.FindObjectsOfTypeAll(typeof(GameObject));
            foreach (var obj in gameObjects) if (obj is GameObject go && go.scene.IsValid() && IsRunLevelName(go.name)) return go.name;
            return "";
        }

        private static bool IsNamedRunLevel(object currentLevel) { return IsRunLevelName(DescribeLevelObject(currentLevel)); }
        private static bool IsRunLevelName(string levelName) { return !string.IsNullOrWhiteSpace(levelName) && levelName.StartsWith("Level - ", StringComparison.Ordinal) && !IsNonGameplayLevelName(levelName); }

        private static bool IsNonGameplayLevelName(string levelName)
        {
            if (string.IsNullOrWhiteSpace(levelName)) return false;
            string lower = levelName.ToLowerInvariant();
            return lower.Contains("lobby") || lower.Contains("menu") || lower.Contains("shop") || lower.Contains("splash") || lower.Contains("post") || lower.Contains("death") || lower.Contains("result") || lower.Contains("summary");
        }

        private static bool IsNonGameplayContext()
        {
            Type runManagerType = AccessTools.TypeByName("RunManager");
            object runManager = ReadMember(runManagerType, "instance");
            return IsNonGameplayLevelName(DescribeLevelObject(ReadMember(runManager, "levelCurrent"))) || IsNonGameplayLevelName(SceneManager.GetActiveScene().name);
        }

        private static string DescribeCurrentLevel(object runManager) { return DescribeLevelObject(ReadMember(runManager, "levelCurrent")); }
        private static string DescribeLevelObject(object currentLevel) { if (currentLevel == null) return "<null>"; if (currentLevel is UnityEngine.Object unityObject) return string.IsNullOrWhiteSpace(unityObject.name) ? unityObject.ToString() : unityObject.name; return currentLevel.ToString(); }

        // ОПТИМИЗАЦИЯ: Кэширование проверок состояния игры, чтобы не убивать ФПС
        private static bool isRunLevelCache = false;
        private static float nextRunLevelCheck = 0f;
        private static bool CachedIsRunLevel(string sceneName)
        {
            if (sceneName != null && IsRunLevelName(sceneName)) return true;
            if (Time.unscaledTime > nextRunLevelCheck)
            {
                object result = InvokeNoArgMethod(AccessTools.TypeByName("SemiFunc"), "RunIsLevel");
                isRunLevelCache = result is bool value && value;
                nextRunLevelCheck = Time.unscaledTime + 1f;
            }
            return isRunLevelCache;
        }

        private static bool isMasterCache = true;
        private static float nextMasterCheck = 0f;
        private static bool CachedIsMasterClient()
        {
            if (Time.unscaledTime > nextMasterCheck)
            {
                object result = InvokeNoArgMethod(AccessTools.TypeByName("SemiFunc"), "IsMasterClientOrSingleplayer");
                isMasterCache = !(result is bool value) || value;
                nextMasterCheck = Time.unscaledTime + 2f;
            }
            return isMasterCache;
        }

        private static float CalculateMapValue()
        {
            Type valuableType = AccessTools.TypeByName("ValuableObject");
            if (valuableType == null) return 0f;
            float total = 0f;
            foreach (var val in UnityEngine.Object.FindObjectsOfType(valuableType)) total += ReadValuableCurrentValue(val);
            return Math.Max(0f, total);
        }

        private static int? ResolveExtractionGoal()
        {
            Type roundDirectorType = AccessTools.TypeByName("RoundDirector");
            object roundDirector = ReadMember(roundDirectorType, "instance");
            object goal = ReadMember(roundDirector, "extractionHaulGoal");
            if (goal == null) return null;
            try { return Math.Max(0, Convert.ToInt32(goal)); } catch { return null; }
        }

        private static Component GetValuableComponent(object source) { if (source is Component component) { Component val = component.GetComponent("ValuableObject"); if (val != null) return val; } if (source is GameObject gameObject) { return gameObject.GetComponent("ValuableObject"); } return null; }
        private static float ReadValuableCurrentValue(object source) { return ReadFloatMember(GetValuableSource(source), "dollarValueCurrent"); }
        private static float ReadValuableOriginalValue(object source) { return ReadFloatMember(GetValuableSource(source), "dollarValueOriginal"); }

        private static void TrackDollarHaulValuable(object source, bool inHaul)
        {
            if (!CachedIsRunLevel(null)) return;
            int key = GetValuableKey(source);
            if (key == 0) return;
            if (inHaul) valuablesInDollarHaul.Add(key); else valuablesInDollarHaul.Remove(key);
        }

        private static bool IsValuableInDollarHaul(object source)
        {
            int key = GetValuableKey(source);
            if (key != 0 && valuablesInDollarHaul.Contains(key)) return true;
            object roundDirector = ReadMember(AccessTools.TypeByName("RoundDirector"), "instance");
            if (!(ReadMember(roundDirector, "dollarHaulList") is IEnumerable dollarHaulList)) return false;
            foreach (object item in dollarHaulList) { if (item == null) continue; int itemKey = GetValuableKey(item); if (key != 0 && itemKey == key) return true; if (ReferencesSameUnityObject(source, item)) return true; }
            return false;
        }

        private static int GetValuableKey(object source)
        {
            object valuable = GetValuableSource(source);
            if (valuable == null) return 0;
            object photonView = ReadMember(valuable, "photonView");
            int photonViewId = ReadIntMember(photonView, "ViewID");
            if (photonViewId > 0) return photonViewId;
            if (valuable is UnityEngine.Object unityObject) return unityObject.GetInstanceID();
            return 0;
        }

        private static bool ReferencesSameUnityObject(object left, object right)
        {
            int leftId = GetUnityObjectId(left);
            if (leftId == 0) return false;
            if (leftId == GetUnityObjectId(right)) return true;
            Component lv = GetValuableComponent(left), rv = GetValuableComponent(right);
            if (lv != null && rv != null && lv.GetInstanceID() == rv.GetInstanceID()) return true;
            GameObject lg = GetGameObject(left), rg = GetGameObject(right);
            return lg != null && rg != null && lg.GetInstanceID() == rg.GetInstanceID();
        }

        private static int GetUnityObjectId(object source) { return source is UnityEngine.Object unityObject ? unityObject.GetInstanceID() : 0; }
        private static GameObject GetGameObject(object source) { if (source is GameObject gameObject) return gameObject; if (source is Component component) return component.gameObject; return null; }
        private static object GetValuableSource(object source) { Component valuable = GetValuableComponent(source); return valuable != null ? valuable : source; }
        private static float ReadFloatMember(object source, string memberName) { object value = ReadMember(source, memberName); if (value == null) return 0f; try { return Convert.ToSingle(value, CultureInfo.InvariantCulture); } catch { return 0f; } }
        private static int ReadIntMember(object source, string memberName) { object value = ReadMember(source, memberName); if (value == null) return 0; try { return Convert.ToInt32(value, CultureInfo.InvariantCulture); } catch { return 0; } }

        private string ResolveCurrentLevelName()
        {
            Type runManagerType = AccessTools.TypeByName("RunManager");
            object runManager = ReadMember(runManagerType, "instance");
            object currentLevel = ReadMember(runManager, "levelCurrent");
            string levelName = DescribeLevelObject(currentLevel);
            return levelName == "<null>" ? "" : levelName;
        }

        private void SyncLevelToOverlay(int level, string levelName)
        {
            lastSyncedLevel = level;
            if (gameObject.activeInHierarchy) StartCoroutine(PostLevel(level, levelName));
            lastSyncedUpgrades.Clear();
            pendingUpgradeKeys.Clear();
            for (int index = 0; index < TrackedPlayerUpgrades.Length; index++) pendingUpgradeKeys.Add(TrackedPlayerUpgrades[index].Key);
            nextUpgradeSyncAt = Time.realtimeSinceStartup + 2f;
        }

        private void SyncPlayerUpgradesIfChanged(HashSet<string> onlyKeys = null)
        {
            Type statsManagerType = AccessTools.TypeByName("StatsManager");
            object statsManager = ReadMember(statsManagerType, "instance");
            if (statsManager == null) return;

            var upgradesByPlayer = new Dictionary<string, Dictionary<string, int>>();

            for (int index = 0; index < TrackedPlayerUpgrades.Length; index++)
            {
                KeyValuePair<string, string> binding = TrackedPlayerUpgrades[index];
                if (onlyKeys != null && !onlyKeys.Contains(binding.Key)) continue;

                object upgradesValue = ReadMember(statsManager, binding.Value);
                if (!(upgradesValue is IDictionary upgrades)) continue;

                foreach (DictionaryEntry entry in upgrades)
                {
                    string steamId = entry.Key?.ToString();
                    if (string.IsNullOrEmpty(steamId)) continue;

                    int value = 0;
                    try { value = Math.Max(0, Convert.ToInt32(entry.Value)); } catch { continue; }

                    string cacheKey = steamId + "_" + binding.Key;
                    if (lastSyncedUpgrades.TryGetValue(cacheKey, out int previousValue) && previousValue == value) continue;

                    lastSyncedUpgrades[cacheKey] = value;

                    if (!upgradesByPlayer.TryGetValue(steamId, out var playerUpgrades))
                    {
                        playerUpgrades = new Dictionary<string, int>();
                        upgradesByPlayer[steamId] = playerUpgrades;
                    }
                    playerUpgrades[binding.Key] = value;
                }
            }

            if (upgradesByPlayer.Count == 0) return;

            string localId = ResolveLocalPlayerSteamId();
            var json = new StringBuilder("{\"localSteamId\":\"").Append(localId).Append("\",\"players\":[");
            int playerCount = 0;

            foreach (var kvp in upgradesByPlayer)
            {
                string steamId = kvp.Key;
                var playerUpgrades = kvp.Value;
                if (playerUpgrades.Count == 0) continue;

                string playerName = ResolvePlayerName(steamId) ?? ("Игрок " + steamId.Substring(0, Math.Min(4, steamId.Length)));

                if (playerCount++ > 0) json.Append(',');
                json.Append("{\"steamId\":\"").Append(steamId).Append("\",\"name\":\"").Append(EscapeJson(playerName)).Append("\",\"upgrades\":{");

                int count = 0;
                foreach (var upg in playerUpgrades)
                {
                    if (count++ > 0) json.Append(',');
                    json.Append('\"').Append(upg.Key).Append("\":").Append(upg.Value);
                }
                json.Append("}}");
            }
            json.Append("]}");

            if (gameObject.activeInHierarchy) StartCoroutine(PostPlayerUpgrades(json.ToString(), playerCount));
        }

        private static string ResolvePlayerName(string steamId)
        {
            Type playerAvatarType = AccessTools.TypeByName("PlayerAvatar");
            if (playerAvatarType == null) return null;

            UnityEngine.Object[] avatars = Resources.FindObjectsOfTypeAll(playerAvatarType);
            foreach (var avatar in avatars)
            {
                string id = ReadMember(avatar, "steamID") as string;
                if (id == steamId)
                {
                    return ReadMember(avatar, "playerName") as string;
                }
            }
            return null;
        }

        private static string ResolveLocalPlayerSteamId()
        {
            Type playerControllerType = AccessTools.TypeByName("PlayerController");
            object playerController = ReadMember(playerControllerType, "instance");
            string steamId = ReadMember(playerController, "playerSteamID") as string;
            if (!string.IsNullOrEmpty(steamId)) return steamId;

            object playerAvatar = ReadMember(playerController, "playerAvatarScript");
            return ReadMember(playerAvatar, "steamID") as string;
        }

        private static Camera FindBestCamera()
        {
            if (Camera.main != null) return Camera.main;
            Camera[] cameras = Camera.allCameras;
            Camera best = null;
            float bestDepth = float.MinValue;
            foreach (Camera camera in cameras)
            {
                if (camera == null || !camera.isActiveAndEnabled) continue;
                if (camera.depth >= bestDepth) { best = camera; bestDepth = camera.depth; }
            }
            return best;
        }

        private List<EnemyCandidate> FindEnemyCandidates()
        {
            var result = new List<EnemyCandidate>();
            var seenRoots = new HashSet<int>();
            foreach (Component component in GetKnownEnemyParentsSnapshot()) AddEnemyCandidate(result, seenRoots, component);
            foreach (Component component in FindSpawnedEnemiesFromDirector()) AddEnemyCandidate(result, seenRoots, component);
            float now = Time.realtimeSinceStartup;
            bool runBroadDiscovery = !rosterPublished && result.Count == 0 && broadEnemyDiscoveryAttempts < 3 && now >= nextBroadEnemyDiscoveryAt;
            if (runBroadDiscovery)
            {
                broadEnemyDiscoveryAttempts++;
                nextBroadEnemyDiscoveryAt = now + 5f;
                foreach (Component component in FindComponentsByTypeName("EnemyParent")) AddEnemyCandidate(result, seenRoots, component);
                if (result.Count == 0) foreach (Component component in FindComponentsByTypeName("Enemy")) AddEnemyCandidate(result, seenRoots, component);
            }
            return result;
        }

        private static void RegisterEnemyParent(Component component)
        {
            if (component == null) return;
            lock (enemyLock)
            {
                knownEnemyParents.RemoveAll((enemy) => enemy == null);
                if (!knownEnemyParents.Contains(component))
                {
                    knownEnemyParents.Add(component);
                    if (Plugin.instance != null) { Plugin.instance.enemyRosterDirty = true; Plugin.instance.nextScanAt = 0f; }
                }
            }
        }

        private static List<Component> GetKnownEnemyParentsSnapshot()
        {
            lock (enemyLock) { knownEnemyParents.RemoveAll((enemy) => enemy == null); return new List<Component>(knownEnemyParents); }
        }

        private static IEnumerable<Component> FindSpawnedEnemiesFromDirector(bool allowExpensiveFallback = false)
        {
            Type directorType = Type.GetType("EnemyDirector, Assembly-CSharp");
            if (directorType == null) yield break;
            object instance = ReadMember(directorType, "instance");
            if (instance != null) { foreach (Component component in EnumerateSpawnedEnemies(instance)) yield return component; yield break; }
            if (!allowExpensiveFallback) yield break;
            UnityEngine.Object[] directors = Resources.FindObjectsOfTypeAll(directorType);
            foreach (UnityEngine.Object director in directors) foreach (Component component in EnumerateSpawnedEnemies(director)) yield return component;
        }

        private static IEnumerable<Component> EnumerateSpawnedEnemies(object director)
        {
            object spawned = ReadMember(director, "enemiesSpawned");
            if (!(spawned is IEnumerable enumerable)) yield break;
            foreach (object item in enumerable) if (item is Component component) yield return component;
        }

        private static IEnumerable<Component> FindComponentsByTypeName(string typeName)
        {
            Type type = Type.GetType(typeName + ", Assembly-CSharp");
            if (type == null || !typeof(Component).IsAssignableFrom(type)) yield break;
            UnityEngine.Object[] objects = Resources.FindObjectsOfTypeAll(type);
            foreach (UnityEngine.Object obj in objects) if (obj is Component component) yield return component;
        }

        private static void AddEnemyCandidate(List<EnemyCandidate> result, HashSet<int> seenRoots, Component component)
        {
            if (component == null) return;
            GameObject root = GetEnemyRoot(component);
            if (root == null || !root.activeInHierarchy) return;
            Component enemyParent = component.GetType().Name == "EnemyParent" ? component : ReadMember(component, "EnemyParent") as Component;
            if (enemyParent != null) RegisterEnemyParent(enemyParent);
            int id = root.GetInstanceID();
            if (!seenRoots.Add(id)) return;
            result.Add(new EnemyCandidate { Component = component, Root = root, Center = GetObjectCenter(root) });
        }

        private static bool LooksLikeEnemyComponent(Component component)
        {
            string typeName = component.GetType().Name;
            if (typeName == "EnemyParent" || typeName == "Enemy" || typeName == "EnemyAvatar") return true;
            if (typeName.StartsWith("Enemy", StringComparison.OrdinalIgnoreCase)) return true;
            return FindKnownMonster(component.gameObject.name) != null;
        }

        private static GameObject GetEnemyRoot(Component component)
        {
            if (component.GetType().Name == "Enemy") return component.gameObject;
            if (component.GetType().Name == "EnemyParent")
            {
                object linkedEnemy = ReadMember(component, "Enemy");
                return linkedEnemy is Component enemyComponent ? enemyComponent.gameObject : null;
            }
            return component.gameObject;
        }

        private static Vector3 GetObjectCenter(GameObject root)
        {
            Component enemy = root.GetComponent("Enemy");
            if (enemy != null) { object centerTransform = ReadMember(enemy, "CenterTransform"); if (centerTransform is Transform transform) return transform.position; }
            Renderer renderer = root.GetComponentInChildren<Renderer>();
            if (renderer != null) return renderer.bounds.center;
            Collider collider = root.GetComponentInChildren<Collider>();
            if (collider != null) return collider.bounds.center;
            return root.transform.position + Vector3.up;
        }

        private static string ResolveMonsterName(Component component)
        {
            if (component == null) return null;
            Component enemyParent = component.GetType().Name == "EnemyParent" ? component : ReadMember(component, "EnemyParent") as Component;
            if (enemyParent == null) return null;
            return FindKnownMonster(ReadMember(enemyParent, "enemyName") as string);
        }

        private static bool ShouldUseLegacyVisionFallback(Component enemyParent)
        {
            string monsterName = ResolveMonsterName(enemyParent);
            return monsterName != null && PlayerVisionLegacyFallbackMonsters.Contains(monsterName);
        }

        private static bool IsEnemyParentPlayerClose(Component enemyParent) { return ReadMember(enemyParent, "playerClose") is bool b && b; }
        private static bool IsEnemyParentPlayerVeryClose(Component enemyParent) { return ReadMember(enemyParent, "playerVeryClose") is bool b && b; }

        private bool IsEnemyOnScreenVisible(Component enemyOnScreen)
        {
            return ReadMember(enemyOnScreen, "OnScreenLocal") is bool isOnScreen && isOnScreen && (!(ReadMember(enemyOnScreen, "CulledLocal") is bool isCulled) || !isCulled);
        }

        private static IEnumerator WatchBlindEnemyPlayerClose(IEnumerator inner, Component enemyParent)
        {
            bool wasPlayerClose = IsEnemyParentPlayerClose(enemyParent);
            bool wasPlayerVeryClose = instance != null && IsEnemyParentPlayerVeryClose(enemyParent);
            while (inner.MoveNext())
            {
                yield return inner.Current;
                Plugin plugin = instance;
                if (plugin == null || !plugin.gameplayActive || enemyParent == null) continue;
                bool isPlayerClose = IsEnemyParentPlayerClose(enemyParent);
                bool isPlayerVeryClose = IsEnemyParentPlayerVeryClose(enemyParent);
                if (isPlayerClose != wasPlayerClose || isPlayerVeryClose != wasPlayerVeryClose) plugin.SyncEnemyParentStatusChanged(enemyParent);
                if (isPlayerVeryClose && !wasPlayerVeryClose && (!plugin.preferPlayerVisionDetection.Value || !HasEnemyOnScreen(enemyParent) || ShouldUseLegacyVisionFallback(enemyParent))) plugin.HandleBlindEnemyPlayerVeryClose(enemyParent);
                wasPlayerClose = isPlayerClose; wasPlayerVeryClose = isPlayerVeryClose;
            }
        }

        private static IEnumerator WatchEnemyOnScreen(IEnumerator inner, Component enemyOnScreen)
        {
            Component enemyParent = null; int instanceId = 0; bool encounterHandled = false;
            while (inner.MoveNext())
            {
                yield return inner.Current;
                Plugin plugin = instance;
                if (plugin == null || !plugin.gameplayActive || enemyOnScreen == null || encounterHandled || !plugin.preferPlayerVisionDetection.Value) continue;
                if (enemyParent == null) enemyParent = GetEnemyParentFromOnScreen(enemyOnScreen);
                if (enemyParent == null) continue;
                if (instanceId == 0) instanceId = ResolveEnemyInstanceId(enemyParent);
                if (instanceId != 0 && IsEnemySent(instanceId)) { encounterHandled = true; continue; }
                if (!plugin.IsEnemyOnScreenVisible(enemyOnScreen)) continue;
                plugin.HandleEnemyOnScreenVisible(enemyParent, ref instanceId);
                if (instanceId != 0 && IsEnemySent(instanceId)) encounterHandled = true;
            }
        }

        private void HandleBlindEnemyPlayerVeryClose(Component enemyParent)
        {
            if (enemyParent == null || HasEnemyVision(enemyParent)) return;
            if (preferPlayerVisionDetection.Value && HasEnemyOnScreen(enemyParent) && !ShouldUseLegacyVisionFallback(enemyParent)) return;
            int instanceId = ResolveEnemyInstanceId(enemyParent);
            if (instanceId == 0 || IsEnemySent(instanceId)) return;
            RegisterEnemyParent(enemyParent);
            string monsterName = null;
            if (PublishEnemyParentEncounter(enemyParent, ref instanceId, ref monsterName)) return;
            pendingEncounterIds.Add(instanceId); enemyRosterDirty = true; nextScanAt = 0f;
        }

        private void HandleEnemyOnScreenVisible(Component enemyParent, ref int instanceId)
        {
            if (!preferPlayerVisionDetection.Value || enemyParent == null) return;
            if (instanceId == 0) instanceId = ResolveEnemyInstanceId(enemyParent);
            if (instanceId == 0 || IsEnemySent(instanceId)) return;
            RegisterEnemyParent(enemyParent);
            string monsterName = null;
            if (PublishEnemyParentEncounter(enemyParent, ref instanceId, ref monsterName)) return;
            pendingEncounterIds.Add(instanceId); enemyRosterDirty = true; nextScanAt = 0f;
        }

        private bool PublishEnemyParentEncounter(Component enemyParent, ref int instanceId, ref string monsterName)
        {
            if (!rosterPublished || enemyParent == null) return false;
            GameObject root = GetEnemyRoot(enemyParent);
            if (root == null) return false;
            if (instanceId == 0) instanceId = root.GetInstanceID();
            if (instanceId == 0 || IsEnemySent(instanceId)) return true;
            if (monsterName == null) { monsterName = ResolveMonsterName(enemyParent); if (monsterName != null) resolvedMonsterNames[instanceId] = monsterName; }
            if (monsterName == null) return false;
            if (!TryMarkEnemySent(instanceId)) return true;
            var candidate = new EnemyCandidate { Component = enemyParent, Root = root, Center = GetObjectCenter(root) };
            MarkMonsterSeen(monsterName, candidate);
            if (gameObject.activeInHierarchy) StartCoroutine(PostSeenMonster(monsterName, instanceId));
            SyncEnemyParentStatusChanged(enemyParent);
            return true;
        }

        private void HandleEnemyVisionTrigger(object vision, int playerId)
        {
            if (!gameplayActive || vision == null || playerId != GetLocalPlayerViewId()) return;
            if (!TryGetVisionEnemyCache(vision, out VisionEnemyCache visionEnemy)) return;
            Component enemyParent = visionEnemy.EnemyParent;
            if (preferPlayerVisionDetection.Value && HasEnemyOnScreen(enemyParent) && !ShouldUseLegacyVisionFallback(enemyParent)) return;
            int instanceId = visionEnemy.InstanceId;
            if (instanceId == 0 || IsEnemySent(instanceId) || pendingEncounterIds.Contains(instanceId)) return;
            RegisterEnemyParent(enemyParent);
            string monsterName = null;
            if (PublishEnemyParentEncounter(enemyParent, ref instanceId, ref monsterName)) { pendingEncounterIds.Remove(instanceId); return; }
            pendingEncounterIds.Add(instanceId); enemyRosterDirty = true; nextScanAt = 0f;
        }

        private bool TryGetVisionEnemyCache(object vision, out VisionEnemyCache visionEnemy)
        {
            visionEnemy = default;
            int visionId = GetUnityObjectId(vision);
            if (visionId != 0 && visionEnemyCacheByVisionId.TryGetValue(visionId, out visionEnemy) && visionEnemy.EnemyParent != null && visionEnemy.InstanceId != 0) return true;
            Component enemy = ReadMember(vision, "Enemy") as Component;
            Component enemyParent = ReadMember(enemy, "EnemyParent") as Component;
            if (enemyParent == null) return false;
            int instanceId = ResolveEnemyInstanceId(enemyParent);
            if (instanceId == 0) return false;
            visionEnemy = new VisionEnemyCache { EnemyParent = enemyParent, InstanceId = instanceId };
            if (visionId != 0) visionEnemyCacheByVisionId[visionId] = visionEnemy;
            return true;
        }

        private void TryPublishPendingVisionEncounters(List<ResolvedEnemyCandidate> resolvedEnemies)
        {
            if (pendingEncounterIds.Count == 0) return;
            foreach (var resolvedEnemy in resolvedEnemies)
            {
                int instanceId = resolvedEnemy.Candidate.Root.GetInstanceID();
                if (!pendingEncounterIds.Contains(instanceId)) continue;
                Component enemyParent = GetEnemyParent(resolvedEnemy.Candidate);
                string monsterName = resolvedEnemy.MonsterName;
                int publishId = instanceId;
                if (PublishEnemyParentEncounter(enemyParent, ref publishId, ref monsterName)) pendingEncounterIds.Remove(instanceId);
            }
        }

        private static bool HasEnemyVision(Component enemyParent)
        {
            if (enemyParent == null) return false;
            Plugin plugin = instance;
            if (plugin != null)
            {
                int parentId = enemyParent.GetInstanceID();
                if (plugin.enemyHasVisionByParentId.TryGetValue(parentId, out bool cachedValue)) return cachedValue;
                bool value = ReadEnemyHasVision(enemyParent);
                plugin.enemyHasVisionByParentId[parentId] = value;
                return value;
            }
            return ReadEnemyHasVision(enemyParent);
        }

        private static bool ReadEnemyHasVision(Component enemyParent) { return ReadMember(ReadMember(enemyParent, "Enemy") as Component, "HasVision") is bool b && b; }
        private static bool HasEnemyOnScreen(Component enemyParent)
        {
            if (enemyParent == null) return false;
            Plugin plugin = instance;
            if (plugin != null)
            {
                int parentId = enemyParent.GetInstanceID();
                if (plugin.enemyHasOnScreenByParentId.TryGetValue(parentId, out bool cachedValue)) return cachedValue;
                bool value = ReadEnemyHasOnScreen(enemyParent);
                plugin.enemyHasOnScreenByParentId[parentId] = value;
                return value;
            }
            return ReadEnemyHasOnScreen(enemyParent);
        }
        private static bool ReadEnemyHasOnScreen(Component enemyParent) { Component enemy = ReadMember(enemyParent, "Enemy") as Component; if (ReadMember(enemy, "HasOnScreen") is bool value) return value; return enemy != null && enemy.GetComponent("EnemyOnScreen") != null; }
        private static Component GetEnemyParentFromOnScreen(Component enemyOnScreen) { if (enemyOnScreen == null) return null; Component enemy = ReadMember(enemyOnScreen, "Enemy") as Component; if (enemy == null) enemy = enemyOnScreen.GetComponent("Enemy"); return ReadMember(enemy, "EnemyParent") as Component; }
        private static int ResolveEnemyInstanceId(Component enemyParent) { GameObject root = enemyParent == null ? null : GetEnemyRoot(enemyParent); return root == null ? 0 : root.GetInstanceID(); }

        private int GetLocalPlayerViewId() { if (cachedLocalPlayerViewId != int.MinValue) return cachedLocalPlayerViewId; cachedLocalPlayerViewId = ResolveLocalPlayerViewId(); return cachedLocalPlayerViewId; }
        private static int ResolveLocalPlayerViewId()
        {
            object localViewId = InvokeNoArgMethod(AccessTools.TypeByName("SemiFunc"), "PhotonViewIDPlayerAvatarLocal");
            if (localViewId != null) try { return Convert.ToInt32(localViewId, CultureInfo.InvariantCulture); } catch { }
            object player = InvokeNoArgMethod(AccessTools.TypeByName("SemiFunc"), "PlayerAvatarLocal");
            if (player == null) player = ReadMember(AccessTools.TypeByName("PlayerAvatar"), "instance");
            return ReadIntMember(ReadMember(player, "photonView"), "ViewID");
        }

        // ОПТИМИЗАЦИЯ РЕФЛЕКСИИ (Убирает лаги GC при чтении переменных)
        private static object ReadMember(object source, string memberName)
        {
            if (source == null) return null;
            Type type = source as Type ?? source.GetType();

            Dictionary<string, MemberInfo> typeCache;
            lock (reflectionCacheLock)
            {
                if (!fastMemberCache.TryGetValue(type, out typeCache))
                {
                    typeCache = new Dictionary<string, MemberInfo>();
                    fastMemberCache[type] = typeCache;
                }
            }

            MemberInfo member;
            lock (reflectionCacheLock)
            {
                if (!typeCache.TryGetValue(memberName, out member))
                {
                    const BindingFlags flags = BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Instance | BindingFlags.Static;
                    member = type.GetField(memberName, flags) as MemberInfo ?? type.GetProperty(memberName, flags);
                    typeCache[memberName] = member;
                }
            }

            if (member == null) return null;
            if (member is FieldInfo field) return (!field.IsStatic && source is Type) ? null : field.GetValue(field.IsStatic ? null : source);
            if (member is PropertyInfo property && property.CanRead)
            {
                var getter = property.GetGetMethod(true);
                return (getter != null && (getter.IsStatic || !(source is Type))) ? property.GetValue(getter.IsStatic ? null : source, null) : null;
            }
            return null;
        }

        private static object InvokeNoArgMethod(object source, string methodName)
        {
            if (source == null) return null;
            Type type = source as Type ?? source.GetType();

            Dictionary<string, MethodInfo> typeCache;
            lock (reflectionCacheLock)
            {
                if (!fastNoArgMethodCache.TryGetValue(type, out typeCache))
                {
                    typeCache = new Dictionary<string, MethodInfo>();
                    fastNoArgMethodCache[type] = typeCache;
                }
            }

            MethodInfo method;
            lock (reflectionCacheLock)
            {
                if (!typeCache.TryGetValue(methodName, out method))
                {
                    const BindingFlags flags = BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Instance | BindingFlags.Static;
                    method = type.GetMethod(methodName, flags, null, Type.EmptyTypes, null);
                    typeCache[methodName] = method;
                }
            }

            if (method == null || (!method.IsStatic && source is Type)) return null;
            try { return method.Invoke(method.IsStatic ? null : source, null); } catch { return null; }
        }

        private static Task<string> QueueNetworkRequest(Func<string> request)
        {
            lock (networkQueueLock)
            {
                Task<string> queued = networkQueueTail.ContinueWith(_ => request(), CancellationToken.None, TaskContinuationOptions.None, TaskScheduler.Default);
                networkQueueTail = queued; return queued;
            }
        }

        private IEnumerator PostSeenMonster(string monsterName, int instanceId)
        {
            string json = "{\"name\":\"" + EscapeJson(monsterName) + "\",\"id\":" + instanceId + "}";
            Task<string> request = QueueNetworkRequest(() => SendHttpPost(endpoint.Value, json));
            while (!request.IsCompleted) yield return null;
        }

        private IEnumerator PostMonsterRoster(string json)
        {
            Task<string> request = QueueNetworkRequest(() => SendHttpPost(BuildSiblingEndpoint(levelEndpoint.Value, "/api/roster"), json));
            while (!request.IsCompleted) yield return null;
        }

        private IEnumerator PostMonsterStatuses(string json, bool coalesce = false)
        {
            int requestVersion = coalesce ? Interlocked.Increment(ref latestMonsterStatusRequestVersion) : 0;
            Task<string> request = QueueNetworkRequest(() => !coalesce || requestVersion == Volatile.Read(ref latestMonsterStatusRequestVersion) ? SendHttpPost(BuildSiblingEndpoint(levelEndpoint.Value, "/api/monster-status"), json) : "SKIPPED:Superseded monster status snapshot.");
            while (!request.IsCompleted) yield return null;
        }

        private IEnumerator PostLevel(int level, string levelName)
        {
            string json = "{\"level\":" + level + ",\"levelName\":\"" + EscapeJson(levelName ?? "") + "\"}";
            Task<string> request = QueueNetworkRequest(() => SendHttpPost(levelEndpoint.Value, json));
            while (!request.IsCompleted) yield return null;
        }

        private IEnumerator PostVisibility(bool visible)
        {
            Task<string> request = QueueNetworkRequest(() => SendHttpPost(BuildSiblingEndpoint(levelEndpoint.Value, "/api/visibility"), "{\"visible\":" + (visible ? "true" : "false") + "}"));
            while (!request.IsCompleted) yield return null;
        }

        private IEnumerator PostCursorState(bool visible)
        {
            Task<string> request = QueueNetworkRequest(() => SendHttpPost(BuildSiblingEndpoint(levelEndpoint.Value, "/api/cursor"), "{\"visible\":" + (visible ? "true" : "false") + "}"));
            while (!request.IsCompleted) yield return null;
        }

        private IEnumerator PostTabHidden(bool hidden)
        {
            Task<string> request = QueueNetworkRequest(() => SendHttpPost(BuildSiblingEndpoint(levelEndpoint.Value, "/api/tab-hidden"), "{\"hidden\":" + (hidden ? "true" : "false") + "}"));
            while (!request.IsCompleted) yield return null;
        }

        private IEnumerator PostPlayerUpgrades(string json, int changedCount)
        {
            Task<string> request = QueueNetworkRequest(() => SendHttpPost(BuildSiblingEndpoint(levelEndpoint.Value, "/api/upgrades"), json));
            while (!request.IsCompleted) yield return null;
        }

        private IEnumerator PostMapValue(int value, int initial, int lost, int? goal)
        {
            string json = "{\"value\":" + value.ToString(CultureInfo.InvariantCulture) + ",\"initial\":" + initial.ToString(CultureInfo.InvariantCulture) + ",\"lost\":" + lost.ToString(CultureInfo.InvariantCulture);
            if (goal.HasValue) json += ",\"goal\":" + goal.Value.ToString(CultureInfo.InvariantCulture); json += "}";
            int requestVersion = Interlocked.Increment(ref latestMapValueRequestVersion);
            Task<string> request = QueueNetworkRequest(() => requestVersion == Volatile.Read(ref latestMapValueRequestVersion) ? SendHttpPost(BuildSiblingEndpoint(levelEndpoint.Value, "/api/map-value"), json) : "SKIPPED:Superseded map value snapshot.");
            while (!request.IsCompleted) yield return null;
        }

        private static string SendStateLevelFallback(int level, string levelEndpointUrl)
        {
            string stateEndpoint = BuildSiblingEndpoint(levelEndpointUrl, "/api/state");
            return SendHttpPost(stateEndpoint, "{\"state\":" + BuildFallbackStateJson(level, SendHttpGet(stateEndpoint)) + "}");
        }

        private static string BuildSiblingEndpoint(string endpointUrl, string path)
        {
            try { var uri = new Uri(endpointUrl); return uri.Scheme + "://" + uri.Host + (uri.IsDefaultPort ? "" : ":" + uri.Port) + path; }
            catch { return endpointUrl.Replace("/api/level", path).Replace("/api/monster-seen", path); }
        }

        private static string BuildFallbackStateJson(int level, string getStateResult)
        {
            string stateObject = ExtractJsonObjectProperty(ExtractHttpBody(getStateResult), "state");
            if (string.IsNullOrWhiteSpace(stateObject)) stateObject = "{}";
            stateObject = SetJsonNumberProperty(stateObject, "level", level);
            stateObject = SetJsonBooleanProperty(stateObject, "gameplayVisible", true);
            stateObject = SetJsonNumberProperty(stateObject, "seconds", 0);
            stateObject = SetJsonBooleanProperty(stateObject, "running", true);
            stateObject = SetJsonRawProperty(stateObject, "startedAt", ((long)(DateTime.UtcNow - new DateTime(1970, 1, 1, 0, 0, 0, DateTimeKind.Utc)).TotalMilliseconds).ToString(CultureInfo.InvariantCulture));
            stateObject = SetJsonRawProperty(stateObject, "monsters", "[]");
            stateObject = SetJsonNumberProperty(stateObject, "mapValue", 0);
            stateObject = SetJsonNumberProperty(stateObject, "mapValueInitial", 0);
            stateObject = SetJsonRawProperty(stateObject, "mapValueGoal", "null");
            stateObject = SetJsonNumberProperty(stateObject, "lostValue", 0);
            return stateObject;
        }

        private static string SetJsonNumberProperty(string json, string name, int value) { return SetJsonRawProperty(json, name, value.ToString()); }
        private static string SetJsonBooleanProperty(string json, string name, bool value) { return SetJsonRawProperty(json, name, value ? "true" : "false"); }
        private static string SetJsonRawProperty(string json, string name, string value)
        {
            string pattern = "(\"" + Regex.Escape(name) + "\"\\s*:\\s*)(null|true|false|-?\\d+(?:\\.\\d+)?|\"(?:\\\\.|[^\"])*\"|\\[[\\s\\S]*?\\]|\\{[\\s\\S]*?\\})";
            var regex = new Regex(pattern);
            if (regex.IsMatch(json)) return regex.Replace(json, "$1" + value, 1);
            string trimmed = string.IsNullOrWhiteSpace(json) ? "{}" : json.Trim();
            if (trimmed == "{}") return "{\"" + name + "\":" + value + "}";
            return trimmed.Substring(0, trimmed.Length - 1) + ",\"" + name + "\":" + value + "}";
        }

        private static string ExtractJsonObjectProperty(string json, string name)
        {
            if (string.IsNullOrWhiteSpace(json)) return null;
            int markerIndex = json.IndexOf("\"" + name + "\"", StringComparison.Ordinal);
            if (markerIndex < 0) return null;
            int colonIndex = json.IndexOf(':', markerIndex + name.Length + 2);
            if (colonIndex < 0) return null;
            int start = json.IndexOf('{', colonIndex + 1);
            if (start < 0) return null;

            int depth = 0; bool inString = false; bool escaped = false;
            for (int index = start; index < json.Length; index++)
            {
                char ch = json[index];
                if (escaped) { escaped = false; continue; }
                if (ch == '\\' && inString) { escaped = true; continue; }
                if (ch == '"') { inString = !inString; continue; }
                if (inString) continue;
                if (ch == '{') depth++;
                else if (ch == '}') { depth--; if (depth == 0) return json.Substring(start, index - start + 1); }
            }
            return null;
        }

        private static bool IsHttpSuccess(string result) { return result != null && (result.StartsWith("HTTP/1.1 2", StringComparison.Ordinal) || result.StartsWith("HTTP/1.0 2", StringComparison.Ordinal)); }
        private static string TrimHttpResult(string result) { if (string.IsNullOrEmpty(result)) return "empty response"; int lineEnd = result.IndexOf('\n'); string firstLine = lineEnd >= 0 ? result.Substring(0, lineEnd) : result; if (firstLine.StartsWith("ERROR:", StringComparison.Ordinal)) return firstLine.Substring(6); return firstLine.Trim(); }

        private static string SendHttpPost(string endpointUrl, string json)
        {
            try
            {
                var uri = new Uri(endpointUrl);
                if (!string.Equals(uri.Scheme, "http", StringComparison.OrdinalIgnoreCase)) return "ERROR:Only http:// endpoints are supported by the raw bridge client.";
                int port = uri.IsDefaultPort ? 80 : uri.Port;
                byte[] body = Encoding.UTF8.GetBytes(json);
                string path = string.IsNullOrEmpty(uri.PathAndQuery) ? "/" : uri.PathAndQuery;

                using (var client = new TcpClient())
                {
                    IAsyncResult connect = client.BeginConnect(uri.Host, port, null, null);
                    if (!connect.AsyncWaitHandle.WaitOne(TimeSpan.FromSeconds(2))) return "ERROR:Connection timed out.";
                    client.EndConnect(connect); client.ReceiveTimeout = 2000; client.SendTimeout = 2000;

                    using (NetworkStream stream = client.GetStream())
                    using (var writer = new StreamWriter(stream, new UTF8Encoding(false), 1024, true))
                    using (var reader = new StreamReader(stream, Encoding.UTF8, false, 1024, true))
                    {
                        writer.NewLine = "\r\n";
                        writer.WriteLine("POST " + path + " HTTP/1.1");
                        writer.WriteLine("Host: " + uri.Host + ":" + port);
                        writer.WriteLine("Content-Type: application/json");
                        writer.WriteLine("Content-Length: " + body.Length);
                        writer.WriteLine("Connection: close");
                        writer.WriteLine();
                        writer.Flush();
                        stream.Write(body, 0, body.Length);
                        stream.Flush();
                        return ReadHttpResponse(reader);
                    }
                }
            }
            catch (Exception error) { return "ERROR:" + error.GetType().Name + ": " + error.Message; }
        }

        private static string SendHttpGet(string endpointUrl)
        {
            try
            {
                var uri = new Uri(endpointUrl);
                if (!string.Equals(uri.Scheme, "http", StringComparison.OrdinalIgnoreCase)) return "ERROR:Only http:// endpoints are supported by the raw bridge client.";
                int port = uri.IsDefaultPort ? 80 : uri.Port;
                string path = string.IsNullOrEmpty(uri.PathAndQuery) ? "/" : uri.PathAndQuery;

                using (var client = new TcpClient())
                {
                    IAsyncResult connect = client.BeginConnect(uri.Host, port, null, null);
                    if (!connect.AsyncWaitHandle.WaitOne(TimeSpan.FromSeconds(2))) return "ERROR:Connection timed out.";
                    client.EndConnect(connect); client.ReceiveTimeout = 2000; client.SendTimeout = 2000;

                    using (NetworkStream stream = client.GetStream())
                    using (var writer = new StreamWriter(stream, new UTF8Encoding(false), 1024, true))
                    using (var reader = new StreamReader(stream, Encoding.UTF8, false, 1024, true))
                    {
                        writer.NewLine = "\r\n";
                        writer.WriteLine("GET " + path + " HTTP/1.1");
                        writer.WriteLine("Host: " + uri.Host + ":" + port);
                        writer.WriteLine("Connection: close");
                        writer.WriteLine();
                        writer.Flush();
                        return ReadHttpResponse(reader);
                    }
                }
            }
            catch (Exception error) { return "ERROR:" + error.GetType().Name + ": " + error.Message; }
        }

        private static string ReadHttpResponse(StreamReader reader)
        {
            string status = reader.ReadLine();
            if (string.IsNullOrEmpty(status)) return "ERROR:Empty HTTP response.";
            var builder = new StringBuilder(); builder.AppendLine(status);
            string line; while ((line = reader.ReadLine()) != null) builder.AppendLine(line);
            return builder.ToString();
        }

        private static string ExtractHttpBody(string response)
        {
            if (string.IsNullOrEmpty(response)) return "";
            int split = response.IndexOf("\r\n\r\n", StringComparison.Ordinal);
            if (split >= 0) return response.Substring(split + 4);
            split = response.IndexOf("\n\n", StringComparison.Ordinal);
            return split >= 0 ? response.Substring(split + 2) : "";
        }

        private static string FindKnownMonster(string raw)
        {
            string key = Normalize(raw);
            foreach (KeyValuePair<string, string> pair in KnownMonsters) if (key.Contains(pair.Key)) return pair.Value;
            return null;
        }

        private static string Normalize(string value)
        {
            if (string.IsNullOrWhiteSpace(value)) return "";
            var builder = new StringBuilder(value.Length);
            foreach (char ch in value.ToLowerInvariant()) if ((ch >= 'a' && ch <= 'z') || (ch >= '0' && ch <= '9')) builder.Append(ch);
            return builder.ToString();
        }

        private static string EscapeJson(string value) { return value.Replace("\\", "\\\\").Replace("\"", "\\\""); }

        private struct EnemyCandidate { public Component Component; public GameObject Root; public Vector3 Center; }
        private struct ResolvedEnemyCandidate { public EnemyCandidate Candidate; public string MonsterName; }
        private struct VisionEnemyCache { public Component EnemyParent; public int InstanceId; }
    }
}