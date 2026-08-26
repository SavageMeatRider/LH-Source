package com.LastHit.Source;

import net.minecraft.client.Minecraft;
import net.minecraft.client.gui.FontRenderer;
import net.minecraft.client.gui.Gui;
import net.minecraft.client.gui.GuiScreen;
import net.minecraft.client.gui.ScaledResolution;
import net.minecraft.entity.player.EntityPlayer;
import net.minecraft.network.play.client.C01PacketChatMessage;
import net.minecraft.scoreboard.Score;
import net.minecraft.scoreboard.ScoreObjective;
import net.minecraft.scoreboard.ScorePlayerTeam;
import net.minecraft.scoreboard.Scoreboard;
import net.minecraft.util.ChatComponentText;
import net.minecraftforge.client.event.ClientChatReceivedEvent;
import net.minecraftforge.client.event.RenderGameOverlayEvent;
import net.minecraftforge.client.event.RenderGameOverlayEvent.ElementType;
import net.minecraftforge.common.MinecraftForge;
import net.minecraftforge.event.world.WorldEvent;
import net.minecraftforge.fml.common.Mod;
import net.minecraftforge.fml.common.Mod.EventHandler;
import net.minecraftforge.fml.common.event.FMLInitializationEvent;
import net.minecraftforge.fml.common.eventhandler.SubscribeEvent;
import net.minecraftforge.fml.common.gameevent.InputEvent;
import net.minecraftforge.fml.common.gameevent.TickEvent;
import net.minecraftforge.fml.common.gameevent.TickEvent.Phase;
import org.lwjgl.input.Keyboard;

import java.io.IOException;
import java.util.Locale;
import java.util.Random;
import java.util.concurrent.Executors;
import java.util.concurrent.ScheduledExecutorService;
import java.util.concurrent.ThreadFactory;
import java.util.concurrent.TimeUnit;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

@Mod(
        modid = "AutoHit",
        name = "AutoHit",
        version = "1.0",
        acceptedMinecraftVersions = "[1.8.9]",
        clientSideOnly = true
)
public class AutoHit {

    private static final int PING_WINDOW = 30;
    private static final double MAX_FIRE_WINDOW = 5000.0;
    private static final double CAL_RATE = 0.8;
    private static final int MAX_HITS = 3;

    public enum TimeUnit2 {
        NANOSECOND  ("Nanosecond",  "ns",  1L,             1_000_000_000L,         1L,          50_000_000L),
        PICOSECOND  ("Picosecond",  "ps",  1_000L,         1_000_000_000_000L,     1L,          50_000_000_000L),
        FEMTOSECOND ("Femtosecond", "fs",  1_000_000L,     1_000_000_000_000_000L, 1L,          50_000_000_000_000L),
        ATTOSECOND  ("Attosecond",  "as",  1_000_000_000L, Long.MAX_VALUE / 2,     1L,          Long.MAX_VALUE / 100),
        ZEPTOSECOND ("Zeptosecond", "zs",  Long.MAX_VALUE / 1_000_000_000L, Long.MAX_VALUE / 2, 1L, Long.MAX_VALUE / 100),
        YOCTOSECOND ("Yoctosecond", "ys",  Long.MAX_VALUE / 1_000_000_000L, Long.MAX_VALUE / 2, 1L, Long.MAX_VALUE / 100),
        PLANCK       ("Planck",     "tP",  Long.MAX_VALUE / 1_000_000_000L, Long.MAX_VALUE / 2, 1L, Long.MAX_VALUE / 100);

        final String displayName;
        final String suffix;

        final long unitsPerNs;

        final long unitsPerSecond;

        final long schedulerPeriodNs;

        final long defaultFireWindowUnits;

        TimeUnit2(String dn, String s, long upns, long ups, long spns, long dfwu) {
            displayName      = dn;
            suffix           = s;
            unitsPerNs       = upns;
            unitsPerSecond   = ups;
            schedulerPeriodNs= spns;
            defaultFireWindowUnits = dfwu;
        }

        double msToUnits(double ms) {

            return ms * 1_000_000.0 * unitsPerNs;
        }

        long nsToUnits(long ns) {
            return ns * unitsPerNs;
        }

        double unitsToMs(long units) {
            if (unitsPerNs == 0) return 0;
            return (double) units / unitsPerNs / 1_000_000.0;
        }

        String format(long units) {

            return String.format("%,d %s", units, suffix);
        }
    }

    private volatile TimeUnit2 timeMode = TimeUnit2.NANOSECOND;

    private final Minecraft mc = Minecraft.getMinecraft();
    private final Random rng = new Random();

    private final double[] pingSamples = new double[PING_WINDOW];
    private int pingSampleIdx = 0;
    private int pingSampleCount = 0;
    private double currentPingMs = 60.0;
    private double averagePingMs = 60.0;
    private double p95PingMs = 80.0;

    private volatile double pingMultiplier = 1.0;

    private double calibrationOffsetMs = 50.0;
    private double targetRegistrationMs = 0.001;

    private double timerSeconds = 0.0;
    private long timerSyncTimeNs = 0L;
    private boolean timerActive = false;

    private boolean moduleEnabled = true;

    private volatile int toggleKeyCode = 19;
    private volatile boolean bindingKey = false;

    private EntityPlayer target = null;
    private boolean attackExecuted = false;
    private int hitCount = 0;
    private long lastAttackTimeMs = 0L;
    private double firedAtRemainingMs = -1.0;

    private int roundNumber = 0;
    private int lastSeenSeconds = -1;

    private volatile boolean nanoFireEnabled = true;
    private ScheduledExecutorService nanoFireScheduler = null;

    private volatile boolean smoothTimerEnabled = true;

    private volatile boolean chatPingEnabled = false;

    private volatile long chatPingSendTimeNs = 0L;

    private volatile boolean chatPingAwaitingResponse = false;

    private volatile double chatPingMs = 60.0;

    private final double[] chatPingSamples = new double[10];
    private int chatPingSampleIdx = 0;
    private int chatPingSampleCount = 0;

    private ScheduledExecutorService chatPingScheduler = null;

    private static final String[] PROBE_SUFFIXES = {
            "xkqzwv", "mfptjr", "bvlnsq", "hzdywx", "cgrjkp",
            "qnbxzm", "wltfhd", "yprcvs", "dkzxqb", "fmwnjt"
    };
    private int probeSuffixIdx = 0;

    private static final double activateTimeSeconds = 1.0;

    private volatile long nanoTimerRemUnits = 0L;

    private volatile double nanoTimerRemMs = 0.0;
    private ScheduledExecutorService nanoTimerScheduler = null;

    private ScheduledExecutorService scoreboardScheduler;
    private ScheduledExecutorService aimLockScheduler;

    private ScheduledExecutorService nanoPingScheduler = null;

    private static final double NANO_PING_ALPHA = 0.5;

    private volatile boolean aimLockActive = false;

    private static final long TARGET_SEARCH_INTERVAL_MS = 333L;
    private long lastTargetSearchTimeMs = 0L;

    private boolean iWas = false;
    private boolean rWas = false;

    private static final Pattern MINUTES_PATTERN = Pattern.compile("(\\d+)m");
    private static final Pattern SECONDS_PATTERN = Pattern.compile("(\\d+)s");
    private static final Pattern EXPLOSION_PATTERN = Pattern.compile("explosion", 2);

    private final SimpleHUD hud = new SimpleHUD();

    @EventHandler
    public void init(FMLInitializationEvent event) {
        MinecraftForge.EVENT_BUS.register(this);
        hud.visible = true;

        scoreboardScheduler = Executors.newSingleThreadScheduledExecutor(new ThreadFactory() {
            public Thread newThread(Runnable r) {
                Thread t = new Thread(r, "TNTTag-Scoreboard");
                t.setDaemon(true);
                return t;
            }
        });

        scoreboardScheduler.scheduleAtFixedRate(new Runnable() {
            public void run() {
                try {
                    if (mc.theWorld != null && mc.thePlayer != null) {
                        monitorScoreboard();
                    }
                } catch (Exception ignored) {
                }
            }
        }, 0L, 1L, TimeUnit.MILLISECONDS);

        aimLockScheduler = Executors.newSingleThreadScheduledExecutor(new ThreadFactory() {
            public Thread newThread(Runnable r) {
                Thread t = new Thread(r, "TNTTag-AimLock");
                t.setDaemon(true);
                return t;
            }
        });

        aimLockScheduler.scheduleAtFixedRate(new Runnable() {
            public void run() {
                try {
                    tickAimLock();
                } catch (Exception ignored) {
                }
            }
        }, 0L, 1L, TimeUnit.MILLISECONDS);

    }

    private void startNanoFireScheduler() {
        if (nanoFireScheduler != null && !nanoFireScheduler.isShutdown()) return;
        nanoFireScheduler = Executors.newSingleThreadScheduledExecutor(new ThreadFactory() {
            public Thread newThread(Runnable r) {
                Thread t = new Thread(r, "TNTTag-NanoFire");
                t.setDaemon(true);
                t.setPriority(Thread.MAX_PRIORITY);
                return t;
            }
        });

        nanoFireScheduler.scheduleAtFixedRate(new Runnable() {
            public void run() {
                try {
                    tickNanoFire();
                } catch (Exception ignored) {
                }
            }
        }, 0L, 1L, TimeUnit.NANOSECONDS);
    }

    private void stopNanoFireScheduler() {
        if (nanoFireScheduler != null) {
            nanoFireScheduler.shutdownNow();
            nanoFireScheduler = null;
        }
    }

    private void tickNanoFire() {
        if (!moduleEnabled || !timerActive || attackExecuted || target == null) return;
        if (mc.thePlayer == null || mc.theWorld == null) return;

        long remainingNs = calculateRemainingNs();
        long remainingUnits = timeMode.nsToUnits(remainingNs);
        long fireWindowUnits = calculateFireWindowUnits();

        if (remainingUnits <= fireWindowUnits) {
            double remainingMs = remainingNs / 1_000_000.0;
            executeAutoAttack(remainingMs);
        }
    }

    private void startNanoTimerScheduler() {
        if (nanoTimerScheduler != null && !nanoTimerScheduler.isShutdown()) return;
        nanoTimerScheduler = Executors.newSingleThreadScheduledExecutor(new ThreadFactory() {
            public Thread newThread(Runnable r) {
                Thread t = new Thread(r, "TNTTag-NanoTimer");
                t.setDaemon(true);
                t.setPriority(Thread.MAX_PRIORITY);
                return t;
            }
        });

        long periodNs = smoothTimerEnabled ? 1_000_000L : 50_000_000L;
        nanoTimerScheduler.scheduleAtFixedRate(new Runnable() {
            public void run() {
                try {
                    if (timerActive) {
                        long remNs = calculateRemainingNs();
                        nanoTimerRemUnits = timeMode.nsToUnits(remNs);
                        nanoTimerRemMs = remNs / 1_000_000.0;
                    }
                } catch (Exception ignored) {
                }
            }
        }, 0L, periodNs, TimeUnit.NANOSECONDS);
    }

    private void stopNanoTimerScheduler() {
        if (nanoTimerScheduler != null) {
            nanoTimerScheduler.shutdownNow();
            nanoTimerScheduler = null;
        }
    }

    private void startChatPingScheduler() {
        if (chatPingScheduler != null && !chatPingScheduler.isShutdown()) return;
        chatPingScheduler = Executors.newSingleThreadScheduledExecutor(new ThreadFactory() {
            public Thread newThread(Runnable r) {
                Thread t = new Thread(r, "TNTTag-ChatPing");
                t.setDaemon(true);
                return t;
            }
        });
        chatPingScheduler.scheduleAtFixedRate(new Runnable() {
            public void run() {
                try {
                    tickChatPingProbe();
                } catch (Exception ignored) {
                }
            }
        }, 0L, 50L, TimeUnit.MILLISECONDS);
    }

    private void stopChatPingScheduler() {
        if (chatPingScheduler != null) {
            chatPingScheduler.shutdownNow();
            chatPingScheduler = null;
        }
        chatPingAwaitingResponse = false;
        chatPingSendTimeNs = 0L;
    }

    private void tickChatPingProbe() {
        if (!chatPingEnabled || !timerActive) return;
        if (mc.thePlayer == null || mc.theWorld == null) return;

        String cmd = "/" + PROBE_SUFFIXES[probeSuffixIdx % PROBE_SUFFIXES.length];
        probeSuffixIdx++;

        chatPingSendTimeNs = System.nanoTime();
        chatPingAwaitingResponse = true;

        if (mc.getNetHandler() != null) {
            String safe = cmd.length() > 100 ? cmd.substring(0, 100) : cmd;
            mc.getNetHandler().addToSendQueue(new C01PacketChatMessage(safe));
        }
    }

    private void onChatPingResponse(String rawMessage) {
        if (!chatPingEnabled || !chatPingAwaitingResponse || chatPingSendTimeNs == 0L) return;

        String lower = rawMessage.toLowerCase(Locale.ROOT);
        boolean isCooldown    = lower.contains("wait") || lower.contains("slow down") || lower.contains("cooldown");
        boolean isUnknownCmd  = lower.contains("unknown command") || lower.contains("command") || lower.contains("found");

        if (!isCooldown && !isUnknownCmd) return;

        long rttNs = System.nanoTime() - chatPingSendTimeNs;
        chatPingAwaitingResponse = false;

        double rttMs = rttNs / 1_000_000.0;

        if (rttMs < 1.0 || rttMs > 2000.0) return;

        chatPingSamples[chatPingSampleIdx % 10] = rttMs;
        chatPingSampleIdx++;
        if (chatPingSampleCount < 10) chatPingSampleCount++;

        double sum = 0.0;
        for (int i = 0; i < chatPingSampleCount; i++) sum += chatPingSamples[i];
        chatPingMs = sum / chatPingSampleCount;

        currentPingMs  = chatPingMs;
        averagePingMs  = chatPingMs;
        p95PingMs      = chatPingMs * 1.1;
    }

    @SubscribeEvent
    public void onChatReceived(ClientChatReceivedEvent event) {
        if (!chatPingEnabled || !chatPingAwaitingResponse) return;
        String msg = event.message.getUnformattedText();
        onChatPingResponse(msg);
    }

    @SubscribeEvent
    public void onKeyInput(InputEvent.KeyInputEvent event) {
        boolean i = Keyboard.isKeyDown(23);
        if (i && !iWas && mc.thePlayer != null && mc.currentScreen == null) {
            mc.displayGuiScreen(new SettingsGui());
        }
        iWas = i;

        boolean r = Keyboard.isKeyDown(toggleKeyCode);
        if (r && !rWas && mc.currentScreen == null) {
            moduleEnabled = !moduleEnabled;
            if (!moduleEnabled) {
                factoryReset("module disabled");
                send("§c[TNTTag] Module disabled.");
            } else {
                send("§a[TNTTag] Module enabled.");
            }
        }
        rWas = r;
    }

    @SubscribeEvent
    public void onWorldLoad(WorldEvent.Load event) {
        factoryReset("world join");
    }

    @SubscribeEvent
    public void onWorldUnload(WorldEvent.Unload event) {
        factoryReset("world leave");
    }

    private void send(String msg) {
        if (mc.thePlayer != null) {
            mc.thePlayer.addChatMessage(new ChatComponentText(msg));
        }
    }

    private void sendSilent(String msg) {
        if (mc.thePlayer != null && mc.getNetHandler() != null) {
            if (msg.length() > 100) msg = msg.substring(0, 100);
            mc.getNetHandler().addToSendQueue(new C01PacketChatMessage(msg));
        }
    }

    private double effectivePingMs() {
        return currentPingMs * pingMultiplier;
    }

    private void clampCalibration() {
        double minAllowedOffset = -(effectivePingMs() * 0.5);
        double maxAllowedOffset = 500.0;
        calibrationOffsetMs = Math.max(minAllowedOffset, Math.min(maxAllowedOffset, calibrationOffsetMs));
    }

    @SubscribeEvent
    public void onClientTick(TickEvent.ClientTickEvent event) {
        if (event.phase == Phase.START) {
            if (!moduleEnabled) {
                hud.update(0, 0, 0, 0, 0, 0, null, false, false);
                return;
            }
            if (mc.theWorld != null && mc.thePlayer != null) {
                if (!timerActive) {
                    target = null;
                    hud.update(0, 0, 0, 0, 0, 0, null, false, false);
                } else {
                    double remainingMs = nanoTimerRemMs > 0 ? nanoTimerRemMs : calculateRemainingTime();
                    if (remainingMs <= 0.0) {
                        timerActive = false;
                        hud.update(0, 0, 0, 0, 0, 0, null, false, false);
                    } else {
                        measurePing();
                        long now = System.currentTimeMillis();
                        if (remainingMs <= activateTimeSeconds * 1000.0) {
                            if (now - lastTargetSearchTimeMs >= TARGET_SEARCH_INTERVAL_MS) {
                                double reach = (double) mc.playerController.getBlockReachDistance();
                                target = findBestTarget(reach);
                                lastTargetSearchTimeMs = now;
                            }

                            if (aimLockActive && (target == null || target.isDead || target.getHealth() <= 0.0f)) {
                                aimLockActive = false;
                            }
                            if (aimLockActive && (mc.thePlayer.isDead || mc.thePlayer.getHealth() <= 0.0f)) {
                                aimLockActive = false;
                            }
                            if (!aimLockActive && target != null && !target.isDead && target.getHealth() > 0.0f
                                    && !mc.thePlayer.isDead && mc.thePlayer.getHealth() > 0.0f) {
                                aimLockActive = true;
                                send("§b[TNTTag] §fAim lock §aON §8→ §e" + target.getName());
                            }
                        } else {
                            if (aimLockActive) {
                                aimLockActive = false;
                            }
                            target = null;
                        }

                        double fireWindowMs = calculateFireWindowMs();
                        long remainingNs = calculateRemainingNs();
                        long fireWindowUnits = calculateFireWindowUnits();
                        long remainingUnits = timeMode.nsToUnits(remainingNs);

                        if (!nanoFireEnabled) {
                            if (!attackExecuted && target != null && remainingUnits <= fireWindowUnits) {
                                executeAutoAttack(remainingMs);
                            }
                        }

                        hud.update(remainingMs, fireWindowMs, targetRegistrationMs,
                                currentPingMs, p95PingMs, 0.0,
                                target, attackExecuted, timerActive);
                    }
                }
            }
        }
    }

    private void monitorScoreboard() {
        Scoreboard sb = mc.theWorld.getScoreboard();
        boolean found = false;

        for (int slot = 0; slot <= 18; slot++) {
            ScoreObjective obj = sb.getObjectiveInDisplaySlot(slot);
            if (obj == null) continue;

            for (Score score : sb.getSortedScores(obj)) {
                String raw = score.getPlayerName();
                ScorePlayerTeam team = sb.getPlayersTeam(raw);
                if (team != null) raw = ScorePlayerTeam.formatPlayerName(team, raw);

                String clean = raw.replaceAll("§[0-9a-fk-or]", "").trim().toLowerCase(Locale.ROOT);
                if (!EXPLOSION_PATTERN.matcher(clean).find()) continue;

                int secs = 0;
                Matcher m = MINUTES_PATTERN.matcher(clean);
                if (m.find()) secs += Integer.parseInt(m.group(1)) * 60;
                m = SECONDS_PATTERN.matcher(clean);
                if (m.find()) secs += Integer.parseInt(m.group(1));

                found = true;
                if (secs == lastSeenSeconds) break;

                if (lastSeenSeconds == -1 || secs > lastSeenSeconds) {
                    if (attackExecuted && firedAtRemainingMs > 0.0) {
                        double estimatedArrivalMs = firedAtRemainingMs - effectivePingMs();
                        double error = estimatedArrivalMs - targetRegistrationMs;
                        double correction = -error * CAL_RATE;
                        calibrationOffsetMs += correction;
                        clampCalibration();
                        send("§6[TNTTag] §8Auto-cal: fired@§f"
                                + String.format("%.3f", firedAtRemainingMs) + "ms "
                                + "§8est.arr=§f" + String.format("%.3f", estimatedArrivalMs) + "ms "
                                + "§8err=§f" + String.format("%+.3f", error) + "ms "
                                + "§8→ off=§f" + String.format("%+.1f", calibrationOffsetMs) + "ms");
                    }

                    roundNumber++;
                    send("§eTNT TAG §fRound §6#" + roundNumber
                            + " §f- §6" + secs + "s "
                            + "§8[target=" + String.format("%.3f", targetRegistrationMs)
                            + "ms off=" + String.format("%+.1f", calibrationOffsetMs)
                            + "ms fw=" + String.format("%.0f", calculateFireWindowMs()) + "ms]");
                    partialRoundReset();
                }

                syncTimer(secs);
                lastSeenSeconds = secs;
                break;
            }
            if (found) break;
        }

        if (!found && lastSeenSeconds != -1) {
            factoryReset("scoreboard gone");
        }
    }

    private void partialRoundReset() {
        timerSyncTimeNs = 0L;
        attackExecuted = false;
        if (aimLockActive) {
            aimLockActive = false;
        }
        send("§e[TNTTag] New round.");
    }

    private void factoryReset() {
        factoryReset("unknown");
    }

    private void factoryReset(String reason) {
        aimLockActive = false;

        target = null;
        attackExecuted = false;
        hitCount = 0;
        lastAttackTimeMs = 0L;
        firedAtRemainingMs = -1.0;
        timerSyncTimeNs = 0L;

        timerSeconds = 0.0;
        timerActive = false;
        lastSeenSeconds = -1;

        lastTargetSearchTimeMs = 0L;
        nanoTimerRemMs = 0.0;
        nanoTimerRemUnits = 0L;

        stopChatPingScheduler();
        stopNanoPingScheduler();

        send("§c[TNTTag] Reset.");
    }

    private void startNanoPingScheduler() {
        if (chatPingEnabled) return;
        if (nanoPingScheduler != null && !nanoPingScheduler.isShutdown()) return;
        nanoPingScheduler = Executors.newSingleThreadScheduledExecutor(new ThreadFactory() {
            public Thread newThread(Runnable r) {
                Thread t = new Thread(r, "TNTTag-NanoPing");
                t.setDaemon(true);
                t.setPriority(Thread.MAX_PRIORITY);
                return t;
            }
        });
        nanoPingScheduler.scheduleAtFixedRate(new Runnable() {
            public void run() {
                try {
                    tickNanoPing();
                } catch (Exception ignored) {
                }
            }
        }, 0L, 1L, TimeUnit.NANOSECONDS);
    }

    private void stopNanoPingScheduler() {
        if (nanoPingScheduler != null) {
            nanoPingScheduler.shutdownNow();
            nanoPingScheduler = null;
        }
    }

    private void tickNanoPing() {
        if (!timerActive || chatPingEnabled) return;
        if (mc.thePlayer == null || mc.theWorld == null || mc.getNetHandler() == null) return;

        try {
            int raw = mc.getNetHandler()
                    .getPlayerInfo(mc.thePlayer.getUniqueID())
                    .getResponseTime();
            if (raw <= 0) return;

            double d = (double) raw;

            currentPingMs = NANO_PING_ALPHA * d + (1.0 - NANO_PING_ALPHA) * currentPingMs;
            averagePingMs = 0.15 * d + 0.85 * averagePingMs;

            pingSamples[pingSampleIdx % PING_WINDOW] = d;
            pingSampleIdx++;
            if (pingSampleCount < PING_WINDOW) pingSampleCount++;

            int filled = pingSampleCount;
            double[] sorted = new double[filled];
            System.arraycopy(pingSamples, 0, sorted, 0, filled);
            for (int i = 1; i < filled; i++) {
                double key = sorted[i];
                int j = i - 1;
                while (j >= 0 && sorted[j] > key) { sorted[j + 1] = sorted[j]; j--; }
                sorted[j + 1] = key;
            }
            int p95idx = Math.min((int) Math.floor(filled * 0.95), filled - 1);
            p95PingMs = sorted[p95idx];
        } catch (Exception ignored) {
        }
    }

    private void syncTimer(int seconds) {
        timerSeconds = seconds;

        if (seconds > 0 && (double) seconds <= activateTimeSeconds + 0.0001) {
            timerSyncTimeNs = System.nanoTime();
            timerActive = true;
            attackExecuted = false;

            if (chatPingEnabled) {

                chatPingSampleIdx = 0;
                chatPingSampleCount = 0;
                chatPingAwaitingResponse = false;
                chatPingSendTimeNs = 0L;
                stopChatPingScheduler();
                startChatPingScheduler();
            } else {
                if (mc.thePlayer != null && mc.theWorld != null) {
                    measurePing();
                }
            }

            if (nanoFireEnabled) {
                stopNanoFireScheduler();
                startNanoFireScheduler();
            }
            stopNanoTimerScheduler();
            startNanoTimerScheduler();

            stopNanoPingScheduler();
            startNanoPingScheduler();
        } else {
            timerActive = false;
            stopChatPingScheduler();
            stopNanoPingScheduler();
        }
    }

    private double calculateRemainingTime() {
        if (timerSyncTimeNs == 0L) return 0.0;
        long elapsedNs = System.nanoTime() - timerSyncTimeNs;
        double elapsedMs = elapsedNs / 1_000_000.0;
        return Math.max(0.0, timerSeconds * 1000.0 - elapsedMs);
    }

    private long calculateRemainingNs() {
        if (timerSyncTimeNs == 0L) return 0L;
        long elapsedNs = System.nanoTime() - timerSyncTimeNs;
        long totalNs = (long) (timerSeconds * 1_000_000_000L);
        return Math.max(0L, totalNs - elapsedNs);
    }

    private long effectivePingNs() {
        return (long) (effectivePingMs() * 1_000_000.0);
    }

    private long calculateFireWindowUnits() {

        long pingUnits = timeMode.nsToUnits(effectivePingNs());
        long minUnits  = timeMode.nsToUnits(effectivePingNs());
        long maxUnits  = timeMode.defaultFireWindowUnits * 100;
        return Math.max(minUnits, Math.min(maxUnits, pingUnits));
    }

    private double calculateFireWindowMs() {
        long fwUnits = calculateFireWindowUnits();
        return timeMode.unitsToMs(fwUnits);
    }

    private void measurePing() {

        if (chatPingEnabled) return;

        try {
            int ping = mc.getNetHandler()
                    .getPlayerInfo(mc.thePlayer.getUniqueID())
                    .getResponseTime();
            if (ping <= 0) return;

            double d = (double) ping;
            currentPingMs = d;
            averagePingMs = 0.15 * d + 0.85 * averagePingMs;

            pingSamples[pingSampleIdx % PING_WINDOW] = d;
            pingSampleIdx++;
            if (pingSampleCount < PING_WINDOW) pingSampleCount++;

            int filled = pingSampleCount;
            double[] sorted = new double[filled];
            System.arraycopy(pingSamples, 0, sorted, 0, filled);

            for (int ii = 1; ii < filled; ii++) {
                double key = sorted[ii];
                int jj = ii - 1;
                while (jj >= 0 && sorted[jj] > key) {
                    sorted[jj + 1] = sorted[jj];
                    jj--;
                }
                sorted[jj + 1] = key;
            }

            int p95idx = Math.min((int) Math.floor(filled * 0.95), filled - 1);
            p95PingMs = sorted[p95idx];
        } catch (Exception ignored) {
        }
    }

    private void tickAimLock() {
        if (!aimLockActive) return;
        if (mc.thePlayer == null || mc.theWorld == null) return;

        EntityPlayer t = target;
        if (t == null || t.isDead || t.getHealth() <= 0.0f) {
            aimLockActive = false;
            return;
        }
        if (mc.thePlayer.isDead || mc.thePlayer.getHealth() <= 0.0f) {
            aimLockActive = false;
            return;
        }

        double ex = mc.thePlayer.posX;
        double ey = mc.thePlayer.posY + mc.thePlayer.getEyeHeight();
        double ez = mc.thePlayer.posZ;

        double tx = t.posX;
        double ty = t.posY + t.getEyeHeight();
        double tz = t.posZ;

        double dx = tx - ex;
        double dy = ty - ey;
        double dz = tz - ez;

        double distXZ = Math.sqrt(dx * dx + dz * dz);

        float yaw = (float) (Math.toDegrees(Math.atan2(dz, dx)) - 90.0);
        float pitch = (float) (-Math.toDegrees(Math.atan2(dy, distXZ)));

        mc.thePlayer.rotationYaw = yaw;
        mc.thePlayer.rotationPitch = pitch;
    }

    private EntityPlayer findBestTarget(double range) {
        EntityPlayer best = null;
        double minDist = range;

        for (EntityPlayer p : mc.theWorld.playerEntities) {
            if (p == mc.thePlayer) continue;
            if (p.isDead) continue;
            if (p.getHealth() <= 0.0f) continue;

            double d = (double) mc.thePlayer.getDistanceToEntity(p);
            if (d <= minDist) {
                minDist = d;
                best = p;
            }
        }
        return best;
    }

    private void executeAutoAttack(double remainingMs) {
        if (target == null || target.isDead) return;

        String taggedName = target.getName();
        attackExecuted = true;
        hitCount++;
        lastAttackTimeMs = System.currentTimeMillis();
        firedAtRemainingMs = remainingMs;

        mc.thePlayer.swingItem();
        mc.playerController.attackEntity(mc.thePlayer, target);

        send("§c⚡ §fTagged §e" + taggedName
                + " §8@ §f" + String.format("%.3f", remainingMs) + "ms "
                + "§8(target=§f" + String.format("%.3f", targetRegistrationMs) + "ms§8)"
                + " §8[hit §f" + hitCount + "§8/§f" + MAX_HITS + "§8]");

        if (hitCount >= MAX_HITS) {
            send("§6[TNTTag] §fMax hits reached (§c" + MAX_HITS + "§f) — factory reset.");
            factoryReset("max hits (" + MAX_HITS + ") reached");
        }
    }

    @SubscribeEvent
    public void onRenderOverlay(RenderGameOverlayEvent.Post event) {
        if (event.type == ElementType.ALL) {
            hud.render();
        }
    }

    private class SimpleHUD extends Gui {

        boolean visible;
        double remMs, fireWindow, targetMs, avgPing, p95Ping, offset;
        EntityPlayer tgt;
        boolean attacked, active;

        private SimpleHUD() {
            visible = true;
        }

        void update(double r, double fw, double tm, double ap, double pp, double o,
                    EntityPlayer t, boolean at, boolean ac) {
            remMs    = r;
            fireWindow = fw;
            targetMs = tm;
            avgPing  = ap;
            p95Ping  = pp;
            offset   = o;
            tgt      = t;
            attacked = at;
            active   = ac;
        }

        void render() {
            if (!visible || mc.theWorld == null) return;

            ScaledResolution sr = new ScaledResolution(mc);
            FontRenderer fr = mc.fontRendererObj;
            int cx = sr.getScaledWidth() / 2;
            int y = 6;

            if (!moduleEnabled) {
                draw(fr, "TNTTag - DISABLED", cx, y, 0xFF4444);
                return;
            }

            if (!active) {
                draw(fr, "TNTTag  [I=settings]", cx, y, 0xAAAAAA);
            } else {

                long remNs = calculateRemainingNs();
                long remUnits = timeMode.nsToUnits(remNs);

                long fwUnits = calculateFireWindowUnits();
                int timerCol = remUnits < fwUnits
                        ? 0xFF4444
                        : (remUnits < fwUnits * 2L ? 0xFFDD22 : 0x44DD44);

                String timerStr = timeMode.format(remUnits);
                draw(fr, timerStr, cx, y, timerCol);
                y += 14;

                String fwStr  = timeMode.format(fwUnits);
                int aimCol    = aimLockActive ? 0x44CCFF : 0x666666;
                String aimStr = aimLockActive ? "[AIM]" : "[---]";
                int statCol   = attacked ? 0x44FF44 : (tgt != null ? 0xFFDD22 : 0x888888);
                String statStr = attacked ? "HIT!" : (tgt != null ? "locked" : "idle");
                int nfCol     = nanoFireEnabled ? 0x44CCFF : 0x555555;
                String nfStr  = nanoFireEnabled ? "[NF]" : "[--]";

                String fwLabel = "FW:" + fwStr + "  ";
                int fwLabelW = fr.getStringWidth(fwLabel);
                int statW    = fr.getStringWidth(statStr);
                int aimW     = fr.getStringWidth("  " + aimStr);
                int nfW      = fr.getStringWidth("  " + nfStr);
                int totalW   = fwLabelW + statW + aimW + nfW;
                int lx = cx - totalW / 2;
                fr.drawStringWithShadow(fwLabel, lx, y, 0x888888);
                lx += fwLabelW;
                fr.drawStringWithShadow(statStr, lx, y, statCol);
                lx += statW;
                fr.drawStringWithShadow("  " + aimStr, lx, y, aimCol);
                lx += aimW;
                fr.drawStringWithShadow("  " + nfStr, lx, y, nfCol);
                y += 12;

                double displayPing = chatPingEnabled ? chatPingMs : currentPingMs;
                String multStr = (pingMultiplier != 1.0)
                        ? String.format(" x%.1f=%.0fms", pingMultiplier, effectivePingMs())
                        : "";
                String pingLine = String.format("ping %.0fms%s  p95 %.0fms", displayPing, multStr, p95Ping);
                draw(fr, pingLine, cx, y, 0x777777);
            }
        }

        private void draw(FontRenderer fr, String s, int cx, int y, int color) {
            int tw = fr.getStringWidth(s.replaceAll("§.", ""));
            fr.drawStringWithShadow(s, cx - tw / 2.0f, y, color);
        }
    }

    private class SettingsGui extends GuiScreen {

        private static final int PANEL_W  = 440;
        private static final int PANEL_H  = 380;
        private static final int ROW_H    = 52;
        private static final int ROW_GAP  = 2;
        private static final int HEADER_H = 88;
        private static final int COL_LABEL_X  = 16;
        private static final int COL_DESC_X   = 148;
        private static final int COL_CTRL_W   = 120;
        private static final int DESC_MAX_W   = 150;

        private static final int COL_BG           = 0xD8080010;
        private static final int COL_PANEL        = 0xF00A0020;
        private static final int COL_PANEL_BORDER = 0xFF6633CC;
        private static final int COL_PANEL_INNER  = 0xFF1A0040;
        private static final int COL_ACCENT_TOP   = 0xFF9955FF;
        private static final int COL_ACCENT_BOT   = 0xFF6622BB;
        private static final int COL_LINE_ACCENT  = 0x886633CC;
        private static final int COL_LINE_SOFT    = 0x1AFFFFFF;
        private static final int COL_ROW_HOVER    = 0x1A9955FF;
        private static final int COL_ROW_ALT      = 0x08FFFFFF;
        private static final int COL_ON_BG        = 0xFF0A1E0A;
        private static final int COL_ON_BORDER    = 0xFF44CC66;
        private static final int COL_ON_GLOW      = 0x3344CC66;
        private static final int COL_OFF_BG       = 0xFF1A0A0A;
        private static final int COL_OFF_BORDER   = 0xFF883333;
        private static final int COL_WHITE        = 0xFFFFFFFF;
        private static final int COL_LAVENDER     = 0xFFCCAAFF;
        private static final int COL_GRAY         = 0xFF999999;
        private static final int COL_DIMGRAY      = 0xFF555577;
        private static final int COL_PURPLE       = 0xFFAA66FF;
        private static final int COL_PURPLE_DIM   = 0xFF7744BB;
        private static final int COL_GOLD         = 0xFFFFCC44;
        private static final int COL_CYAN         = 0xFF55DDFF;

        private static final int BTN_W       = 60;
        private static final int BTN_H       = 16;
        private static final int STEP_BTN_W  = 18;

        private static final int ROW_FIRECHECK = 0;
        private static final int ROW_TIMERSYNC = 1;
        private static final int ROW_PINGMULT  = 2;
        private static final int ROW_TIMEMODE  = 3;
        private static final int ROW_KEYBIND   = 4;
        private static final int NUM_ROWS      = 5;

        private int hoveredRow = -1;
        private int px, py;

        @Override
        public void initGui() {
            px = width  / 2 - PANEL_W / 2;
            py = height / 2 - PANEL_H / 2;
        }

        private int rowTopY(int row) {
            return py + HEADER_H + row * (ROW_H + ROW_GAP);
        }

        @Override
        public void drawScreen(int mouseX, int mouseY, float partialTicks) {
            int cx = width / 2;

            drawRect(0, 0, width, height, COL_BG);

            drawRect(px + 4, py + 4, px + PANEL_W + 4, py + PANEL_H + 4, 0x66000000);

            drawRect(px,     py,     px + PANEL_W,     py + PANEL_H,     COL_PANEL);

            drawRect(px - 1, py - 1, px + PANEL_W + 1, py + PANEL_H + 1, COL_PANEL_BORDER);
            drawRect(px + 1, py + 1, px + PANEL_W - 1, py + PANEL_H - 1, COL_PANEL_INNER);
            drawRect(px + 2, py + 2, px + PANEL_W - 2, py + PANEL_H - 2, COL_PANEL);

            drawPurpleBar(px, py, PANEL_W, 3);

            String title = "TNT TAG ASSIST";
            int tw = fontRendererObj.getStringWidth(title);
            fontRendererObj.drawStringWithShadow(title, cx - tw / 2.0f, py + 10, COL_PURPLE);

            String sub = "Settings   \u00b7   ESC to close";
            int sw = fontRendererObj.getStringWidth(sub);
            fontRendererObj.drawStringWithShadow(sub, cx - sw / 2.0f, py + 22, COL_DIMGRAY);

            drawHLine(px + 14, px + PANEL_W - 14, py + 33, COL_LINE_ACCENT);

            String info = String.format(
                    "ping %.0fms  x%.1f=%.0fms   p95 %.0fms   fw %.1fms",
                    currentPingMs, pingMultiplier, effectivePingMs(), p95PingMs,
                    calculateFireWindowMs());
            int iw = fontRendererObj.getStringWidth(info);
            fontRendererObj.drawStringWithShadow(info, cx - iw / 2.0f, py + 38, COL_GRAY);

            String modeBadge = timeMode.displayName + " mode   [SMOOTH]";
            int mb = fontRendererObj.getStringWidth(modeBadge);
            fontRendererObj.drawStringWithShadow(modeBadge, cx - mb / 2.0f, py + 50, COL_PURPLE_DIM);

            drawHLine(px + 14, px + PANEL_W - 14, py + 63, COL_LINE_ACCENT);

            fontRendererObj.drawStringWithShadow("Setting",     px + COL_LABEL_X + 4,        py + 68, COL_DIMGRAY);
            fontRendererObj.drawStringWithShadow("Description", px + COL_DESC_X,              py + 68, COL_DIMGRAY);
            fontRendererObj.drawStringWithShadow("Control",     px + PANEL_W - COL_CTRL_W + 4, py + 68, COL_DIMGRAY);
            drawHLine(px + 14, px + PANEL_W - 14, py + 78, COL_LINE_SOFT);

            hoveredRow = -1;
            for (int row = 0; row < NUM_ROWS; row++) {
                int ry = rowTopY(row);
                if (isInside(mouseX, mouseY, px + 12, ry, px + PANEL_W - 12, ry + ROW_H)) {
                    hoveredRow = row;
                }
            }

            drawRow(ROW_FIRECHECK, mouseX, mouseY);
            {
                int ry = rowTopY(ROW_FIRECHECK);
                drawLabel(px + COL_LABEL_X + 4, ry + 10, "Fire", "Check", COL_LAVENDER);
                int dy = ry + 7;
                fontRendererObj.drawStringWithShadow("1" + timeMode.suffix + " precision fire detection", px + COL_DESC_X, dy,      COL_GRAY);
                fontRendererObj.drawStringWithShadow("High-priority dedicated thread",                     px + COL_DESC_X, dy + 11, COL_GRAY);
                fontRendererObj.drawStringWithShadow("vs client tick (~50ms fallback)",                    px + COL_DESC_X, dy + 22, COL_DIMGRAY);
                drawToggleButton(ctrlX(), ry + ROW_H / 2 - BTN_H / 2, nanoFireEnabled);
            }
            drawHLine(px + 14, px + PANEL_W - 14, rowTopY(ROW_FIRECHECK) + ROW_H, COL_LINE_SOFT);

            drawRow(ROW_TIMERSYNC, mouseX, mouseY);
            {
                int ry = rowTopY(ROW_TIMERSYNC);
                drawLabel(px + COL_LABEL_X + 4, ry + 10, "Smooth", "Timer", COL_LAVENDER);
                int dy = ry + 7;
                fontRendererObj.drawStringWithShadow("HUD timer updates every 1ms",            px + COL_DESC_X, dy,      COL_GRAY);
                fontRendererObj.drawStringWithShadow("Smooth countdown: 10\u21928\u21926\u21924", px + COL_DESC_X, dy + 11, COL_GRAY);
                fontRendererObj.drawStringWithShadow("OFF = ~50ms updates (jumpy)",            px + COL_DESC_X, dy + 22, COL_DIMGRAY);
                drawToggleButton(ctrlX(), ry + ROW_H / 2 - BTN_H / 2, smoothTimerEnabled);
            }
            drawHLine(px + 14, px + PANEL_W - 14, rowTopY(ROW_TIMERSYNC) + ROW_H, COL_LINE_SOFT);

            drawRow(ROW_PINGMULT, mouseX, mouseY);
            {
                int ry = rowTopY(ROW_PINGMULT);
                drawLabel(px + COL_LABEL_X + 4, ry + 10, "Ping", "Multiplier", COL_LAVENDER);
                int dy = ry + 7;
                fontRendererObj.drawStringWithShadow("Scales ping in fire-window calc",    px + COL_DESC_X, dy,      COL_GRAY);
                fontRendererObj.drawStringWithShadow("Range: 1.0x to 2.0x",               px + COL_DESC_X, dy + 11, COL_GRAY);
                fontRendererObj.drawStringWithShadow(String.format("%.0fms raw \u2192 %.0fms effective",
                        currentPingMs, effectivePingMs()),                                  px + COL_DESC_X, dy + 22, COL_GOLD);
                drawStepControl(ctrlX(), ry + ROW_H / 2 - BTN_H / 2,
                        String.format("%.1fx", pingMultiplier), mouseX, mouseY, COL_GOLD);
            }
            drawHLine(px + 14, px + PANEL_W - 14, rowTopY(ROW_PINGMULT) + ROW_H, COL_LINE_SOFT);

            drawRow(ROW_TIMEMODE, mouseX, mouseY);
            {
                int ry = rowTopY(ROW_TIMEMODE);
                drawLabel(px + COL_LABEL_X + 4, ry + 10, "Time Unit", "Mode", COL_LAVENDER);
                int dy = ry + 7;
                fontRendererObj.drawStringWithShadow("Resolution for timer & fire check",  px + COL_DESC_X, dy,      COL_GRAY);
                fontRendererObj.drawStringWithShadow("Click arrows to cycle units",         px + COL_DESC_X, dy + 11, COL_GRAY);
                fontRendererObj.drawStringWithShadow(timeMode.displayName + " (" + timeMode.suffix + ")",
                        px + COL_DESC_X, dy + 22, COL_PURPLE);
                drawStepControl(ctrlX(), ry + ROW_H / 2 - BTN_H / 2,
                        timeMode.suffix, mouseX, mouseY, COL_PURPLE);
            }
            drawHLine(px + 14, px + PANEL_W - 14, rowTopY(ROW_TIMEMODE) + ROW_H, COL_LINE_SOFT);

            drawRow(ROW_KEYBIND, mouseX, mouseY);
            {
                int ry = rowTopY(ROW_KEYBIND);
                drawLabel(px + COL_LABEL_X + 4, ry + 10, "Toggle", "Key", COL_LAVENDER);
                int dy = ry + 7;
                fontRendererObj.drawStringWithShadow("Key to enable / disable module",    px + COL_DESC_X, dy,      COL_GRAY);
                fontRendererObj.drawStringWithShadow("Click button then press new key",   px + COL_DESC_X, dy + 11, COL_GRAY);
                String keyName = bindingKey ? "[ press key ]" : Keyboard.getKeyName(toggleKeyCode);
                fontRendererObj.drawStringWithShadow("Current: " + keyName,              px + COL_DESC_X, dy + 22, COL_CYAN);
                int bx = ctrlX();
                int by = ry + ROW_H / 2 - BTN_H / 2;
                boolean hovBtn = isInside(mouseX, mouseY, bx, by, bx + BTN_W, by + BTN_H);
                int btnBorder = bindingKey ? COL_ON_BORDER : (hovBtn ? 0xFF8866CC : 0xFF442266);
                int btnBg     = bindingKey ? COL_ON_BG     : (hovBtn ? 0xFF1A0033 : 0xFF0D0019);
                drawRect(bx - 1, by - 1, bx + BTN_W + 1, by + BTN_H + 1, btnBorder);
                drawRect(bx,     by,     bx + BTN_W,     by + BTN_H,     btnBg);
                String btnLabel = bindingKey ? "..." : keyName;
                int blw = fontRendererObj.getStringWidth(btnLabel);
                fontRendererObj.drawStringWithShadow(btnLabel, bx + BTN_W / 2 - blw / 2, by + BTN_H / 2 - 4, COL_CYAN);
            }
            drawHLine(px + 14, px + PANEL_W - 14, rowTopY(ROW_KEYBIND) + ROW_H, COL_LINE_SOFT);

            String hint = Keyboard.getKeyName(toggleKeyCode) + " = toggle module";
            int hw = fontRendererObj.getStringWidth(hint);
            fontRendererObj.drawStringWithShadow(hint, cx - hw / 2.0f, py + PANEL_H - 13, COL_DIMGRAY);
            drawPurpleBar(px, py + PANEL_H - 3, PANEL_W, 3);

            super.drawScreen(mouseX, mouseY, partialTicks);
        }

        private int ctrlX() {
            return px + PANEL_W - COL_CTRL_W;
        }

        private void drawLabel(int x, int y, String line1, String line2, int color) {
            fontRendererObj.drawStringWithShadow(line1, x, y,      color);
            fontRendererObj.drawStringWithShadow(line2, x, y + 11, color);
        }

        private void drawPurpleBar(int bx, int by, int bw, int bh) {
            for (int xi = 0; xi < bw; xi++) {
                float t = (float) xi / bw;

                int r = (int) (0x66 + (0xAA - 0x66) * t);
                int g = (int) (0x22 + (0x66 - 0x22) * t);
                int b = (int) (0xBB + (0xFF - 0xBB) * t);
                drawRect(bx + xi, by, bx + xi + 1, by + bh, 0xFF000000 | (r << 16) | (g << 8) | b);
            }
        }

        private void drawRow(int row, int mouseX, int mouseY) {
            int ry = rowTopY(row);
            int bg = (hoveredRow == row) ? COL_ROW_HOVER : (row % 2 == 0 ? COL_ROW_ALT : 0x00000000);
            drawRect(px + 12, ry, px + PANEL_W - 12, ry + ROW_H, bg);

            if (hoveredRow == row) {
                drawRect(px + 12, ry, px + 14, ry + ROW_H, COL_PURPLE);
            }
        }

        private void drawToggleButton(int bx, int by, boolean on) {
            int bgCol  = on ? COL_ON_BG     : COL_OFF_BG;
            int border = on ? COL_ON_BORDER : COL_OFF_BORDER;
            int labelCol = on ? COL_ON_BORDER : COL_OFF_BORDER;
            drawRect(bx - 1, by - 1, bx + BTN_W + 1, by + BTN_H + 1, border);
            drawRect(bx,     by,     bx + BTN_W,     by + BTN_H,     bgCol);
            String label = on ? "ON" : "OFF";
            int lw = fontRendererObj.getStringWidth(label);
            fontRendererObj.drawStringWithShadow(label, bx + BTN_W / 2 - lw / 2, by + BTN_H / 2 - 4, labelCol);
        }

        private void drawStepControl(int bx, int by, String valLabel, int mouseX, int mouseY, int valColor) {
            boolean hovL = isInside(mouseX, mouseY, bx, by, bx + STEP_BTN_W, by + BTN_H);
            int vlw = fontRendererObj.getStringWidth(valLabel);
            int rbx = bx + STEP_BTN_W + 4 + vlw + 4;
            boolean hovR = isInside(mouseX, mouseY, rbx, by, rbx + STEP_BTN_W, by + BTN_H);

            drawRect(bx - 1, by - 1, bx + STEP_BTN_W + 1, by + BTN_H + 1, hovL ? 0xFF8866CC : 0xFF442266);
            drawRect(bx,     by,     bx + STEP_BTN_W,     by + BTN_H,     hovL ? 0xFF1A0033 : 0xFF0D0019);
            fontRendererObj.drawStringWithShadow("\u25c4", bx + STEP_BTN_W / 2 - 3, by + BTN_H / 2 - 4, COL_PURPLE);

            fontRendererObj.drawStringWithShadow(valLabel, bx + STEP_BTN_W + 4, by + BTN_H / 2 - 4, valColor);

            drawRect(rbx - 1, by - 1, rbx + STEP_BTN_W + 1, by + BTN_H + 1, hovR ? 0xFF8866CC : 0xFF442266);
            drawRect(rbx,     by,     rbx + STEP_BTN_W,     by + BTN_H,     hovR ? 0xFF1A0033 : 0xFF0D0019);
            fontRendererObj.drawStringWithShadow("\u25ba", rbx + STEP_BTN_W / 2 - 3, by + BTN_H / 2 - 4, COL_PURPLE);
        }

        private void drawHLine(int x1, int x2, int y, int color) {
            drawRect(x1, y, x2, y + 1, color);
        }

        private boolean isInside(int mx, int my, int x1, int y1, int x2, int y2) {
            return mx >= x1 && mx <= x2 && my >= y1 && my <= y2;
        }

        @Override
        protected void mouseClicked(int mouseX, int mouseY, int mouseButton) throws IOException {
            super.mouseClicked(mouseX, mouseY, mouseButton);
            if (mouseButton != 0) return;

            {
                int ry = rowTopY(ROW_FIRECHECK);
                if (isInside(mouseX, mouseY, px + 12, ry, px + PANEL_W - 12, ry + ROW_H)) {
                    nanoFireEnabled = !nanoFireEnabled;
                    if (nanoFireEnabled) {
                        startNanoFireScheduler();
                        send("§a[TNTTag] Fire check on.");
                    } else {
                        stopNanoFireScheduler();
                        send("§c[TNTTag] Fire check off.");
                    }
                    return;
                }
            }

            {
                int ry = rowTopY(ROW_TIMERSYNC);
                if (isInside(mouseX, mouseY, px + 12, ry, px + PANEL_W - 12, ry + ROW_H)) {
                    smoothTimerEnabled = !smoothTimerEnabled;
                    stopNanoTimerScheduler();
                    startNanoTimerScheduler();
                    send("§a[TNTTag] Smooth timer " + (smoothTimerEnabled ? "on." : "off."));
                    return;
                }
            }

            {
                int ry = rowTopY(ROW_PINGMULT);
                int bx = ctrlX();
                int by = ry + ROW_H / 2 - BTN_H / 2;
                String val = String.format("%.1fx", pingMultiplier);
                int vlw = fontRendererObj.getStringWidth(val);
                int rbx = bx + STEP_BTN_W + 4 + vlw + 4;

                if (isInside(mouseX, mouseY, bx, by, bx + STEP_BTN_W, by + BTN_H)) {
                    pingMultiplier = Math.max(1.0, Math.round((pingMultiplier - 0.1) * 10.0) / 10.0);
                    send(String.format("§6[TNTTag] §fPing multiplier: §a%.1fx §8(→ §f%.0fms§8)", pingMultiplier, effectivePingMs()));
                    return;
                }
                if (isInside(mouseX, mouseY, rbx, by, rbx + STEP_BTN_W, by + BTN_H)) {
                    pingMultiplier = Math.min(2.0, Math.round((pingMultiplier + 0.1) * 10.0) / 10.0);
                    send(String.format("§6[TNTTag] §fPing multiplier: §a%.1fx §8(→ §f%.0fms§8)", pingMultiplier, effectivePingMs()));
                    return;
                }
            }

            {
                int ry = rowTopY(ROW_TIMEMODE);
                int bx = ctrlX();
                int by = ry + ROW_H / 2 - BTN_H / 2;
                int vlw = fontRendererObj.getStringWidth(timeMode.suffix);
                int rbx = bx + STEP_BTN_W + 4 + vlw + 4;
                TimeUnit2[] modes = TimeUnit2.values();

                if (isInside(mouseX, mouseY, bx, by, bx + STEP_BTN_W, by + BTN_H)) {
                    setTimeMode(modes[(timeMode.ordinal() - 1 + modes.length) % modes.length]);
                    return;
                }
                if (isInside(mouseX, mouseY, rbx, by, rbx + STEP_BTN_W, by + BTN_H)) {
                    setTimeMode(modes[(timeMode.ordinal() + 1) % modes.length]);
                    return;
                }
            }

            {
                int ry = rowTopY(ROW_KEYBIND);
                int bx = ctrlX();
                int by = ry + ROW_H / 2 - BTN_H / 2;
                if (isInside(mouseX, mouseY, bx, by, bx + BTN_W, by + BTN_H)) {
                    bindingKey = true;
                    return;
                }
            }
        }

        @Override
        protected void keyTyped(char typedChar, int keyCode) throws IOException {
            if (bindingKey) {
                if (keyCode != 1) {
                    toggleKeyCode = keyCode;
                    send("§b[TNTTag] Toggle key set to " + Keyboard.getKeyName(keyCode) + ".");
                }
                bindingKey = false;
                return;
            }
            if (keyCode == 1) mc.displayGuiScreen(null);
        }

        @Override
        public boolean doesGuiPauseGame() { return false; }
    }

    private void setTimeMode(TimeUnit2 mode) {
        timeMode = mode;

        if (nanoFireEnabled) {
            stopNanoFireScheduler();
            startNanoFireScheduler();
        }

        stopNanoTimerScheduler();
        startNanoTimerScheduler();

        send("§5[TNTTag] §fTime mode → §5" + mode.displayName
                + " §8(" + mode.suffix + ")  fw=" + mode.format(calculateFireWindowUnits()));
    }
}