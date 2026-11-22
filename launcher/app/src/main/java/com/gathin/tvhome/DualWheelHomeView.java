package com.gathin.tvhome;

import android.app.Activity;
import android.content.BroadcastReceiver;
import android.content.Context;
import android.content.Intent;
import android.content.IntentFilter;
import android.content.pm.ApplicationInfo;
import android.content.pm.PackageManager;
import android.content.pm.ResolveInfo;
import android.graphics.Bitmap;
import android.graphics.BitmapFactory;
import android.graphics.BlendMode;
import android.graphics.Canvas;
import android.graphics.Color;
import android.graphics.LinearGradient;
import android.graphics.Paint;
import android.graphics.Path;
import android.graphics.PorterDuff;
import android.graphics.PorterDuffXfermode;
import android.graphics.RadialGradient;
import android.graphics.RectF;
import android.graphics.Shader;
import android.graphics.Typeface;
import android.media.tv.TvContract;
import android.media.tv.TvInputInfo;
import android.media.tv.TvInputManager;
import android.net.Uri;
import android.os.Build;
import android.provider.Settings;
import android.view.KeyEvent;
import android.view.SoundEffectConstants;
import android.view.View;

import java.io.InputStream;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Calendar;
import java.util.Collections;
import java.util.Comparator;
import java.util.Date;
import java.util.HashSet;
import java.util.List;
import java.util.Locale;
import java.util.Random;
import java.util.Set;

/**
 * Custom Dual-Wheel Android TV Home View for TCL 55" Mini LED TV.
 *
 * Updates per user feedback:
 *  1. 100% Consistent Monochrome White Vector Stroke Icons for ALL apps (Netflix, YouTube,
 *     Prime Video, Disney+, Apple TV, Crunchyroll, BBC iPlayer, BBC Sounds, RTÉ Player,
 *     Proton VPN, Play Store, Browser, etc.) — no clashing colored square app bitmaps.
 *  2. Category Title removed from Top-Left and rendered inside the Center Hub of the Wheels
 *     (Left Wheel hub shows active Category title; Right Wheel hub shows active Item title).
 *  3. Locked 60fps hardware-friendly rendering (pre-baked wallpaper vignette, zero per-frame
 *     allocations, delta-time smooth easing, broader wheel arc, and smooth Center Stage +
 *     Startup Clock transitions).
 */
public final class DualWheelHomeView extends View {

    public static final class WheelItem {
        public final String id;
        public final String label;
        public final String shortLabel;
        public final String title;
        public final String desc;
        public final String iconType;
        public final Intent launchIntent;
        public final String packageName;

        public WheelItem(String id, String label, String shortLabel, String title,
                         String desc, String iconType, Intent launchIntent, String packageName) {
            this.id = id;
            this.label = label;
            this.shortLabel = shortLabel;
            this.title = title;
            this.desc = desc;
            this.iconType = iconType;
            this.launchIntent = launchIntent;
            this.packageName = packageName;
        }
    }

    public static final class WheelCategory {
        public final String id;
        public final String label;
        public final String shortLabel;
        public final String iconType;
        public final List<WheelItem> items = new ArrayList<>();

        public WheelCategory(String id, String label, String shortLabel, String iconType) {
            this.id = id;
            this.label = label;
            this.shortLabel = shortLabel;
            this.iconType = iconType;
        }
    }

    // 28 high-res cropped (1216x640 -> 1520x800 OLED-black) optical-flow + golden bokeh frames (7.0s loop)
    private static final int BH_FRAME_COUNT = 28;
    private static final float BH_FLOW_LOOP_SEC = 7.0f;
    private static final float BH_CROP_X = 200f;
    private static final float BH_CROP_Y = 116f;
    private static final float BH_CROP_W = 1520f;
    private static final float BH_CROP_H = 800f;

    private static final class BgStar {
        final float x, y, size, baseAlpha, period, phase;
        final int r, g, b;
        final boolean isGlint;

        BgStar(float x, float y, float size, int r, int g, int b, float baseAlpha, float period, float phase, boolean isGlint) {
            this.x = x; this.y = y; this.size = size;
            this.r = r; this.g = g; this.b = b;
            this.baseAlpha = baseAlpha; this.period = period; this.phase = phase;
            this.isGlint = isGlint;
        }
    }

    private final List<BgStar> bgStars = new ArrayList<>();
    private float nextMeteorSec = 3.0f;
    private boolean meteorActive = false;
    private float meteorStartSec, meteorDur, meteorSx, meteorSy, meteorVx, meteorVy;
    private RadialGradient millerHaloGrad, millerLitGrad;
    private RadialGradient mannHaloGrad, mannLitGrad;
    private RadialGradient shipBeaconGrad;

    private final Activity activity;
    private final List<WheelCategory> categories = new ArrayList<>();
    private int leftIndex = 0;
    private float leftScroll = 0f;
    private int[] rightIndices = new int[6];
    private float rightScroll = 0f;
    private boolean rightWheelActive = false;

    // Power-On Startup Clock Mode (1.0 = giant clock + edge-on Black Hole, 0.0 = expanded wheels + top-down Black Hole)
    private boolean isStartupClockMode = true;
    private float startupLerp = 1.0f;
    private float startupVelocity = 0.0f;

    // Smooth Center Stage transition when switching items (0.0 -> 1.0)
    private float heroPopProgress = 1.0f;
    private String lastHeroItemId = "";
    private float topDeckWheelTarget = 0f;
    private float topDeckWheelScroll = 0f;

    // TV Power ON / OFF (CRT TV switch-off and smooth dual-wheel entrance) state:
    private boolean isTvPoweredOn = true;
    private float enterProgress = 0.0f; // 0.0 -> 1.0 (Wheels enter from either ends, Black hole appears from nowhere)
    private boolean isCrtPoweringOff = false;
    private float crtOffProgress = 0.0f; // 0.0 -> 1.0 (Vertical collapse -> Horizontal single-point collapse -> Wink out)

    private final Paint crtLinePaint = new Paint(Paint.ANTI_ALIAS_FLAG);
    private final Paint crtGlowPaint = new Paint(Paint.ANTI_ALIAS_FLAG);

    private long lastFrameNanos = 0L;
    private float animTimeSec = 0f;

    // Cached time state (updated once per second to avoid per-frame Calendar/Date allocations)
    private long lastTimeUpdateMs = 0L;
    private String cachedTimeStr = "";
    private String cachedDateStr = "";
    private int cachedTzOffsetMs = 0;

    private final Bitmap[] bhFlowFrames = new Bitmap[BH_FRAME_COUNT];
    private volatile boolean bhFramesReady = false;
    private Bitmap bhTopAlphaBitmap;
    private Bitmap enduranceShipBitmap;
    private final RectF bhDstRect = new RectF();
    private RadialGradient shipBackscatterGrad;
    private Typeface brushTypeface;
    private Typeface sansTypeface;
    private Typeface serifItalicTypeface;

    private final Paint paint = new Paint(Paint.ANTI_ALIAS_FLAG);
    private final Paint bitmapPaint = new Paint(Paint.ANTI_ALIAS_FLAG | Paint.FILTER_BITMAP_FLAG);
    private final Paint bhAddPaint = new Paint(Paint.ANTI_ALIAS_FLAG | Paint.FILTER_BITMAP_FLAG);
    private final Paint glowPaint = new Paint(Paint.ANTI_ALIAS_FLAG);
    private final Paint textPaint = new Paint(Paint.ANTI_ALIAS_FLAG);
    private final Path path = new Path();
    private final RectF rectF = new RectF();
    private final SimpleDateFormat timeFormat = new SimpleDateFormat("h:mm a", Locale.US);
    private final SimpleDateFormat dateFormat = new SimpleDateFormat("d MMM, EEEE", Locale.US);

    private LinearGradient eqHorizonGradient;

    private final BroadcastReceiver screenPowerReceiver = new BroadcastReceiver() {
        @Override
        public void onReceive(Context context, Intent intent) {
            String action = intent != null ? intent.getAction() : "";
            if ("com.gathin.tvhome.ACTION_POWER_KEY".equals(action)) {
                startCrtPowerOff();
            } else if (Intent.ACTION_SCREEN_OFF.equals(action)) {
                onTvScreenOff();
            } else if (Intent.ACTION_SCREEN_ON.equals(action)) {
                onTvScreenOn();
            }
        }
    };

    public DualWheelHomeView(Activity activity) {
        super(activity);
        this.activity = activity;
        setFocusable(true);
        setFocusableInTouchMode(true);

        crtLinePaint.setStyle(Paint.Style.STROKE);
        crtLinePaint.setStrokeCap(Paint.Cap.ROUND);
        crtGlowPaint.setStyle(Paint.Style.STROKE);
        crtGlowPaint.setStrokeCap(Paint.Cap.ROUND);

        isTvPoweredOn = true;
        enterProgress = 0.0f;
        isCrtPoweringOff = false;
        crtOffProgress = 0.0f;

        loadAssets();
        rebuildCategories();
    }

    public void startCrtPowerOff() {
        if (!isTvPoweredOn && !isCrtPoweringOff) return;
        isCrtPoweringOff = true;
        crtOffProgress = 0.0f;
        invalidate();
    }

    public void triggerTvPowerOn() {
        if (isTvPoweredOn && !isCrtPoweringOff) {
            // Already powered on and running; prevent duplicate entrance re-trigger glitch!
            return;
        }
        isTvPoweredOn = true;
        isCrtPoweringOff = false;
        crtOffProgress = 0.0f;
        enterProgress = 0.0f;
        resetToStartupClockMode();
        invalidate();
    }

    public void onTvScreenOn() {
        triggerTvPowerOn();
    }

    public void onTvScreenOff() {
        isTvPoweredOn = false;
        isCrtPoweringOff = false;
        crtOffProgress = 1.0f;
        enterProgress = 0.0f;
        invalidate();
    }

    public void resetToStartupClockMode() {
        leftIndex = 0;
        if (rightIndices != null && rightIndices.length > 0) {
            rightIndices[0] = 0;
        }
        leftScroll = 0f;
        rightScroll = 0f;
        rightWheelActive = false;
        isStartupClockMode = true;
        startupLerp = 1.0f;
        startupVelocity = 0f;
        invalidate();
    }

    @Override
    protected void onAttachedToWindow() {
        super.onAttachedToWindow();
        try {
            IntentFilter filter = new IntentFilter();
            filter.addAction(Intent.ACTION_SCREEN_OFF);
            filter.addAction(Intent.ACTION_SCREEN_ON);
            filter.addAction("com.gathin.tvhome.ACTION_POWER_KEY");
            if (android.os.Build.VERSION.SDK_INT >= 33) {
                activity.registerReceiver(screenPowerReceiver, filter, Context.RECEIVER_NOT_EXPORTED);
            } else {
                activity.registerReceiver(screenPowerReceiver, filter);
            }
        } catch (Exception ignored) {
        }
    }

    @Override
    protected void onDetachedFromWindow() {
        try {
            activity.unregisterReceiver(screenPowerReceiver);
        } catch (Exception ignored) {
        }
        super.onDetachedFromWindow();
    }

    private Bitmap loadLuminanceAlphaBitmap(String assetName) {
        try (InputStream is = activity.getAssets().open(assetName)) {
            Bitmap raw = BitmapFactory.decodeStream(is);
            if (raw == null) return null;
            Bitmap scaled = (raw.getWidth() == 1920 && raw.getHeight() == 1080)
                    ? raw
                    : Bitmap.createScaledBitmap(raw, 1920, 1080, true);
            if (scaled != raw) raw.recycle();

            int w = 1920;
            int h = 1080;
            int[] pixels = new int[w * h];
            scaled.getPixels(pixels, 0, w, 0, 0, w, h);
            scaled.recycle();

            for (int i = 0; i < pixels.length; i++) {
                int c = pixels[i];
                int r0 = Math.max(0, ((c >> 16) & 0xFF) - 2);
                int g0 = Math.max(0, ((c >> 8) & 0xFF) - 3);
                int b0 = Math.max(0, (c & 0xFF) - 6);
                int a = Math.max(r0, Math.max(g0, b0));
                if (a <= 2) {
                    pixels[i] = 0;
                } else {
                    int rOut = Math.min(255, (r0 * 255) / a);
                    int gOut = Math.min(255, (g0 * 255) / a);
                    int bOut = Math.min(255, (b0 * 255) / a);
                    pixels[i] = (a << 24) | (rOut << 16) | (gOut << 8) | bOut;
                }
            }
            Bitmap out = Bitmap.createBitmap(w, h, Bitmap.Config.ARGB_8888);
            out.setPixels(pixels, 0, w, 0, 0, w, h);
            return out;
        } catch (Exception e) {
            return null;
        }
    }

    private void loadAssets() {
        serifItalicTypeface = Typeface.create(Typeface.SERIF, Typeface.BOLD_ITALIC);
        try {
            Typeface outfitMed = new Typeface.Builder(activity.getAssets(), "outfit.ttf")
                    .setFontVariationSettings("'wght' 520")
                    .build();
            Typeface outfitReg = new Typeface.Builder(activity.getAssets(), "outfit.ttf")
                    .setFontVariationSettings("'wght' 380")
                    .build();
            brushTypeface = (outfitMed != null) ? outfitMed : Typeface.createFromAsset(activity.getAssets(), "outfit.ttf");
            sansTypeface = (outfitReg != null) ? outfitReg : brushTypeface;
        } catch (Exception e) {
            try {
                brushTypeface = Typeface.createFromAsset(activity.getAssets(), "outfit.ttf");
                sansTypeface = brushTypeface;
            } catch (Exception ex) {
                brushTypeface = Typeface.create("sans-serif-medium", Typeface.NORMAL);
                sansTypeface = Typeface.create("sans-serif", Typeface.NORMAL);
            }
        }

        // Configure GPU additive blend paint for pure OLED-black frame compositing & exact linear crossfade
        if (Build.VERSION.SDK_INT >= 29) {
            bhAddPaint.setBlendMode(BlendMode.PLUS);
        } else {
            bhAddPaint.setXfermode(new PorterDuffXfermode(PorterDuff.Mode.ADD));
        }

        // Initialize crisp native 1080p pinprick deep-space starfield (zero blurred upscaled JPEGs!)
        bgStars.clear();
        Random starRng = new Random(42019L);
        for (int i = 0; i < 155; i++) {
            float sx = 60f + starRng.nextFloat() * 1800f;
            float sy = 40f + starRng.nextFloat() * 1000f;
            float d = (float) Math.hypot(sx - 960f, sy - 516f);
            if (d < 255f) continue;
            float r = starRng.nextFloat();
            float sz = r < 0.72f ? (0.85f + starRng.nextFloat() * 0.55f)
                    : (r < 0.94f ? (1.4f + starRng.nextFloat() * 0.55f) : (2.0f + starRng.nextFloat() * 0.5f));
            boolean glint = r >= 0.955f;
            float cRoll = starRng.nextFloat();
            int cr = cRoll < 0.30f ? 205 : (cRoll < 0.72f ? 252 : 255);
            int cg = cRoll < 0.30f ? 226 : (cRoll < 0.72f ? 250 : 224);
            int cb = cRoll < 0.30f ? 255 : (cRoll < 0.72f ? 245 : 178);
            bgStars.add(new BgStar(
                    sx, sy, sz, cr, cg, cb,
                    0.30f + starRng.nextFloat() * 0.62f,
                    7.0f + starRng.nextFloat() * 7.0f,
                    starRng.nextFloat() * (float) (Math.PI * 2.0),
                    glint));
        }

        // Pre-allocate shaders for minimalist backlit Miller's Planet (r=34) & Mann's Ice World (r=13)
        float mr = 34f;
        millerHaloGrad = new RadialGradient(
                mr * 0.45f, 0f, mr * 1.48f,
                new int[]{Color.argb(88, 255, 224, 176), Color.argb(26, 130, 185, 235), Color.argb(0, 0, 0, 0)},
                new float[]{0.48f, 0.74f, 1.0f},
                Shader.TileMode.CLAMP);
        millerLitGrad = new RadialGradient(
                mr * 0.72f, 0f, mr * 1.05f,
                new int[]{Color.argb(242, 255, 224, 176), Color.argb(92, 130, 185, 235), Color.BLACK},
                new float[]{0.05f, 0.45f, 1.0f},
                Shader.TileMode.CLAMP);

        float nr = 13f;
        mannHaloGrad = new RadialGradient(
                nr * 0.45f, 0f, nr * 1.48f,
                new int[]{Color.argb(84, 215, 234, 255), Color.argb(24, 120, 165, 225), Color.argb(0, 0, 0, 0)},
                new float[]{0.48f, 0.74f, 1.0f},
                Shader.TileMode.CLAMP);
        mannLitGrad = new RadialGradient(
                nr * 0.72f, 0f, nr * 1.05f,
                new int[]{Color.argb(242, 215, 234, 255), Color.argb(90, 120, 165, 225), Color.BLACK},
                new float[]{0.05f, 0.45f, 1.0f},
                Shader.TileMode.CLAMP);

        shipBeaconGrad = new RadialGradient(
                0f, 0f, 14f,
                new int[]{Color.argb(220, 255, 234, 188), Color.argb(0, 255, 190, 110)},
                new float[]{0f, 1f},
                Shader.TileMode.CLAMP);

        // Load 28 crisp high-res cropped (1216x640 OLED-black) Gargantua frames + Endurance Spacecraft
        BitmapFactory.Options rgb565Opts = new BitmapFactory.Options();
        rgb565Opts.inPreferredConfig = Bitmap.Config.RGB_565;

        try (InputStream is = activity.getAssets().open("bh_frames/bh_00.jpg")) {
            bhFlowFrames[0] = BitmapFactory.decodeStream(is, null, rgb565Opts);
        } catch (Exception ignored) {
        }

        // Decode remaining 27 high-res cropped frames asynchronously for instant cold startup
        new Thread(() -> {
            BitmapFactory.Options bgOpts = new BitmapFactory.Options();
            bgOpts.inPreferredConfig = Bitmap.Config.RGB_565;
            for (int i = 1; i < BH_FRAME_COUNT; i++) {
                String path = String.format(Locale.US, "bh_frames/bh_%02d.jpg", i);
                try (InputStream is = activity.getAssets().open(path)) {
                    bhFlowFrames[i] = BitmapFactory.decodeStream(is, null, bgOpts);
                } catch (Exception ignored) {
                }
            }
            bhFramesReady = true;
            postInvalidateOnAnimation();
        }, "bh-frame-loader").start();

        bhTopAlphaBitmap = loadLuminanceAlphaBitmap("bh_top.jpg");
        try (InputStream is = activity.getAssets().open("endurance_ship.png")) {
            enduranceShipBitmap = BitmapFactory.decodeStream(is);
        } catch (Exception ignored) {
        }

        shipBackscatterGrad = new RadialGradient(
                -30f, -26f, 195f,
                new int[]{Color.argb(42, 255, 212, 152), Color.argb(0, 2, 2, 4)},
                new float[]{0f, 1f},
                Shader.TileMode.CLAMP);

        eqHorizonGradient = new LinearGradient(
                0f, -26f, 0f, 52f,
                new int[]{Color.argb(0, 255, 215, 165), Color.argb(68, 255, 218, 172), Color.argb(0, 255, 215, 165)},
                new float[]{0f, 0.5f, 1f},
                Shader.TileMode.CLAMP);
    }

    private Intent getBestLaunchIntent(PackageManager pm, String pkg) {
        Intent i = pm.getLeanbackLaunchIntentForPackage(pkg);
        if (i == null) i = pm.getLaunchIntentForPackage(pkg);
        return i;
    }

    public void rebuildCategories() {
        categories.clear();
        PackageManager pm = activity.getPackageManager();

        // 1. HOME Category
        WheelCategory homeCat = new WheelCategory("home", "HOME", "Home", "home");
        homeCat.items.add(new WheelItem(
                "ambient_clock", "CLOCK", "Clock", "HOME CLOCK",
                "Press Down or Right on your remote to expand wheels",
                "clock", null, null));

        Intent gameBarIntent = getBestLaunchIntent(pm, "com.tcl.gamebar");
        if (gameBarIntent == null) gameBarIntent = getBestLaunchIntent(pm, "com.tcl.dashboard");
        homeCat.items.add(new WheelItem(
                "game_bar", "GAME BAR", "Game Bar", "144Hz VRR GAME BAR",
                "TCL Mini LED Game Bar & Quick Dashboard",
                "gamepad", gameBarIntent != null ? gameBarIntent : new Intent(Settings.ACTION_DISPLAY_SETTINGS), null));

        homeCat.items.add(new WheelItem(
                "cast_ready", "CHROMECAST", "Cast", "CHROMECAST BUILT-IN",
                "TCL 55\" Mini LED is ready for Google Cast & AirPlay",
                "cast", new Intent(Settings.ACTION_CAST_SETTINGS), null));

        Intent vpnIntent = getBestLaunchIntent(pm, "ch.protonvpn.android");
        if (vpnIntent != null) {
            homeCat.items.add(new WheelItem(
                    "home_vpn", "PROTON VPN", "VPN", "PROTON VPN",
                    "High-speed encrypted VPN tunnel for your TCL TV",
                    "shield", vpnIntent, "ch.protonvpn.android"));
        }

        homeCat.items.add(new WheelItem(
                "screen_saver", "AMBIENT", "Ambient", "AMBIENT MODE",
                "Rest screen in full moonlit canyon clock mode",
                "moon", null, null));
        categories.add(homeCat);

        // 2. SEARCH Category
        WheelCategory searchCat = new WheelCategory("search", "SEARCH", "Search", "search");
        Intent voiceIntent = new Intent(Intent.ACTION_ASSIST);
        searchCat.items.add(new WheelItem(
                "voice_search", "VOICE MIC", "Voice", "GOOGLE ASSISTANT",
                "Search movies, launch apps & control your TCL TV by voice",
                "mic", voiceIntent, null));

        Intent ytSearch = getBestLaunchIntent(pm, "com.google.android.youtube.tv");
        searchCat.items.add(new WheelItem(
                "yt_search", "YOUTUBE", "YouTube", "SEARCH YOUTUBE",
                "Find 4K HDR videos, creators & live streams",
                "youtube", ytSearch, "com.google.android.youtube.tv"));

        Intent nfSearch = getBestLaunchIntent(pm, "com.netflix.ninja");
        if (nfSearch != null) {
            searchCat.items.add(new WheelItem(
                    "nf_search", "NETFLIX", "Netflix", "BROWSE NETFLIX",
                    "Explore 4K Dolby Vision series & films on Netflix",
                    "netflix", nfSearch, "com.netflix.ninja"));
        }

        Intent primeSearch = getBestLaunchIntent(pm, "com.amazon.amazonvideo.livingroom");
        if (primeSearch != null) {
            searchCat.items.add(new WheelItem(
                    "prime_search", "PRIME VIDEO", "Prime", "BROWSE PRIME VIDEO",
                    "Search movies, series & live sports on Prime Video",
                    "prime", primeSearch, "com.amazon.amazonvideo.livingroom"));
        }

        Intent storeIntent = getBestLaunchIntent(pm, "com.android.vending");
        searchCat.items.add(new WheelItem(
                "store_search", "FIND APPS", "Play Store", "GOOGLE PLAY STORE",
                "Search & install new Android TV apps and games",
                "playstore", storeIntent, "com.android.vending"));
        categories.add(searchCat);

        // 3. APPS Category (All user streaming & TV apps with clean monochrome vector icons!)
        WheelCategory appsCat = new WheelCategory("apps", "APPS", "Apps", "apps");
        List<WheelItem> discoveredApps = queryInstalledTvApps(pm);
        appsCat.items.addAll(discoveredApps);
        categories.add(appsCat);

        // 4. LIVE TV Category
        WheelCategory liveTvCat = new WheelCategory("livetv", "LIVE TV", "Live TV", "tv");
        Intent tclTvIntent = getBestLaunchIntent(pm, "com.tcl.tv");
        liveTvCat.items.add(new WheelItem(
                "tcl_tv", "LIVE TUNER", "Tuner", "ANTENNA / LIVE TV",
                "Open TCL Live TV tuner & electronic program guide",
                "tv", tclTvIntent, "com.tcl.tv"));

        Intent channelPlusIntent = getBestLaunchIntent(pm, "com.tcl.channelplus");
        if (channelPlusIntent != null) {
            liveTvCat.items.add(new WheelItem(
                    "tcl_channels", "TCL CHANNEL+", "Channel+", "TCL FREE CHANNELS",
                    "Watch free live streaming channels on TCL Channel+",
                    "channels", channelPlusIntent, "com.tcl.channelplus"));
        }

        Intent rteIntent = getBestLaunchIntent(pm, "com.twentyfouri.tvbridge.rte");
        if (rteIntent != null) {
            liveTvCat.items.add(new WheelItem(
                    "rte_live", "RTÉ PLAYER", "RTÉ Live", "RTÉ PLAYER LIVE",
                    "Watch live Irish TV broadcasts & catch-up on RTÉ Player",
                    "rte_player", rteIntent, "com.twentyfouri.tvbridge.rte"));
        }

        Intent iplayerIntent = getBestLaunchIntent(pm, "bbc.iplayer.android");
        if (iplayerIntent != null) {
            liveTvCat.items.add(new WheelItem(
                    "bbc_live", "BBC iPLAYER", "BBC iPlayer", "BBC iPLAYER LIVE",
                    "Stream live BBC channels & UHD programs",
                    "bbc_iplayer", iplayerIntent, "bbc.iplayer.android"));
        }

        if (ytSearch != null) {
            liveTvCat.items.add(new WheelItem(
                    "yt_live", "YOUTUBE LIVE", "YT Live", "YOUTUBE LIVE STREAMS",
                    "Watch live news, gaming & sports broadcasts on YouTube",
                    "youtube", ytSearch, "com.google.android.youtube.tv"));
        }
        categories.add(liveTvCat);

        // 5. INPUTS Category (Real TvInputManager HDMI ports + USB Media Center)
        WheelCategory inputsCat = new WheelCategory("inputs", "INPUTS", "Inputs", "hdmi_generic");
        populateInputItems(inputsCat, pm);
        categories.add(inputsCat);

        // 6. SETTINGS Category
        WheelCategory settingsCat = new WheelCategory("settings", "SETTINGS", "Settings", "settings");
        settingsCat.items.add(new WheelItem(
                "picture", "PICTURE", "Picture", "MINI LED PICTURE",
                "Local dimming zones, peak brightness & display settings",
                "picture", new Intent(Settings.ACTION_DISPLAY_SETTINGS), null));
        settingsCat.items.add(new WheelItem(
                "sound", "SOUND", "Sound", "AUDIO & eARC",
                "Sound output mode, Dolby Atmos & digital audio settings",
                "sound", new Intent(Settings.ACTION_SOUND_SETTINGS), null));
        settingsCat.items.add(new WheelItem(
                "wifi", "NETWORK", "Wi-Fi", "WI-FI & ETHERNET",
                "High-speed network & internet configuration",
                "wifi", new Intent(Settings.ACTION_WIFI_SETTINGS), null));
        settingsCat.items.add(new WheelItem(
                "bluetooth", "BLUETOOTH", "Bluetooth", "BLUETOOTH & REMOTES",
                "Pair TCL Voice Remote, gamepads & wireless headphones",
                "bluetooth", new Intent(Settings.ACTION_BLUETOOTH_SETTINGS), null));
        settingsCat.items.add(new WheelItem(
                "system", "ALL SETTINGS", "System", "ANDROID TV SETTINGS",
                "Open full Android TV system settings menu",
                "settings", new Intent(Settings.ACTION_SETTINGS), null));
        categories.add(settingsCat);

        rightIndices = new int[categories.size()];
        invalidate();
    }

    private List<WheelItem> queryInstalledTvApps(PackageManager pm) {
        List<WheelItem> result = new ArrayList<>();
        Set<String> seen = new HashSet<>();
        seen.add(activity.getPackageName());
        // Exclude system utilities that already live in dedicated wheels (LIVE TV, INPUTS, SETTINGS, HOME)
        seen.add("com.tcl.tv");
        seen.add("com.android.tv.settings");
        seen.add("com.tcl.suspension");
        seen.add("com.tcl.dashboard");
        seen.add("com.tcl.ui_mediaCenter");
        seen.add("com.tcl.t_solo");

        String[] priorityOrder = new String[]{
                "com.google.android.youtube.tv",
                "com.netflix.ninja",
                "com.amazon.amazonvideo.livingroom",
                "com.disney.disneyplus",
                "com.apple.atve.androidtv.appletv",
                "com.crunchyroll.crunchyroid",
                "bbc.iplayer.android",
                "uk.co.bbc.sounds",
                "com.twentyfouri.tvbridge.rte",
                "ch.protonvpn.android",
                "com.android.vending",
                "com.hisense.odinbrowser",
                "com.tcl.browser"
        };

        Intent leanbackIntent = new Intent(Intent.ACTION_MAIN);
        leanbackIntent.addCategory(Intent.CATEGORY_LEANBACK_LAUNCHER);
        List<ResolveInfo> infos = new ArrayList<>(pm.queryIntentActivities(leanbackIntent, 0));

        Intent mainIntent = new Intent(Intent.ACTION_MAIN);
        mainIntent.addCategory(Intent.CATEGORY_LAUNCHER);
        infos.addAll(pm.queryIntentActivities(mainIntent, 0));

        List<ApplicationInfo> appInfos = new ArrayList<>();
        for (ResolveInfo ri : infos) {
            if (ri.activityInfo == null || ri.activityInfo.applicationInfo == null) continue;
            String pkg = ri.activityInfo.packageName;
            if (seen.add(pkg)) {
                appInfos.add(ri.activityInfo.applicationInfo);
            }
        }

        Collections.sort(appInfos, new Comparator<ApplicationInfo>() {
            @Override
            public int compare(ApplicationInfo a, ApplicationInfo b) {
                int pa = indexOfPriority(priorityOrder, a.packageName);
                int pb = indexOfPriority(priorityOrder, b.packageName);
                if (pa != pb) return Integer.compare(pa, pb);
                String la = String.valueOf(pm.getApplicationLabel(a));
                String lb = String.valueOf(pm.getApplicationLabel(b));
                return la.compareToIgnoreCase(lb);
            }
        });

        for (ApplicationInfo ai : appInfos) {
            String pkg = ai.packageName;
            String rawLabel = cleanAppLabel(pkg, String.valueOf(pm.getApplicationLabel(ai)).trim());
            String upper = rawLabel.toUpperCase(Locale.ROOT);
            String shortLbl = rawLabel.length() > 11 ? rawLabel.substring(0, 11) : rawLabel;
            String iconType = mapPackageToLogo(pkg);
            String desc = mapPackageToDescription(pkg, rawLabel);

            Intent launch = getBestLaunchIntent(pm, pkg);
            if (launch == null) continue;

            result.add(new WheelItem(pkg, upper, shortLbl, upper, desc, iconType, launch, pkg));
        }

        return result;
    }

    private String cleanAppLabel(String pkg, String raw) {
        if (pkg.contains("appletv")) return "Apple TV";
        if (pkg.contains("crunchyroll")) return "Crunchyroll";
        if (pkg.contains("bbc.iplayer")) return "BBC iPlayer";
        if (pkg.contains("bbc.sounds")) return "BBC Sounds";
        if (pkg.contains("rte")) return "RTÉ Player";
        if (pkg.contains("amazonvideo")) return "Prime Video";
        if (pkg.contains("disney")) return "Disney+";
        if (pkg.contains("netflix")) return "Netflix";
        if (pkg.contains("youtube")) return "YouTube";
        if (pkg.contains("protonvpn")) return "Proton VPN";
        if (pkg.equals("com.android.vending")) return "Play Store";
        if (pkg.contains("odinbrowser")) return "BrowseHere";
        if (pkg.contains("tcl.browser")) return "Browser";
        return raw.isEmpty() ? pkg : raw;
    }

    private int indexOfPriority(String[] list, String pkg) {
        for (int i = 0; i < list.length; i++) {
            if (list[i].equals(pkg)) return i;
        }
        return 999;
    }

    private String mapPackageToLogo(String pkg) {
        if (pkg.contains("netflix")) return "netflix";
        if (pkg.contains("youtube") || pkg.contains("smarttube")) return "youtube";
        if (pkg.contains("amazonvideo") || pkg.contains("prime")) return "prime";
        if (pkg.contains("disney")) return "disney";
        if (pkg.contains("appletv") || pkg.contains("apple")) return "appletv";
        if (pkg.contains("crunchyroll")) return "crunchyroll";
        if (pkg.contains("bbc.iplayer")) return "bbc_iplayer";
        if (pkg.contains("bbc.sounds")) return "bbc_sounds";
        if (pkg.contains("rte")) return "rte_player";
        if (pkg.contains("protonvpn") || pkg.contains("vpn")) return "shield";
        if (pkg.equals("com.android.vending")) return "playstore";
        if (pkg.contains("browser") || pkg.contains("odin")) return "browser";
        if (pkg.contains("spotify") || pkg.contains("music")) return "sound";
        return "app_custom";
    }

    private String mapPackageToDescription(String pkg, String label) {
        if (pkg.contains("netflix")) return "Watch 4K Dolby Vision series & movies on Netflix";
        if (pkg.contains("youtube")) return "Watch 4K HDR videos, subscriptions & live streams";
        if (pkg.contains("amazonvideo")) return "Amazon Originals, movies & live sports in HDR10+";
        if (pkg.contains("disney")) return "Stream Disney, Pixar, Marvel, Star Wars & Nat Geo";
        if (pkg.contains("appletv")) return "Apple Originals, 4K Dolby Vision movies & Apple TV+";
        if (pkg.contains("crunchyroll")) return "Stream anime series, movies & simulcasts in HD";
        if (pkg.contains("bbc.iplayer")) return "Watch live BBC TV channels, box sets & UHD specials";
        if (pkg.contains("bbc.sounds")) return "Listen to live BBC radio stations, music mixes & podcasts";
        if (pkg.contains("rte")) return "Watch live Irish TV broadcasts & box sets on RTÉ Player";
        if (pkg.equals("com.android.vending")) return "Browse & install apps on your TCL Google TV";
        if (pkg.contains("protonvpn")) return "High-speed encrypted VPN tunnel for your TCL TV";
        if (pkg.contains("browser")) return "Browse the web on your 55\" Mini LED screen";
        return "Launch " + label + " on your TCL 55\" Mini LED TV";
    }

    private void populateInputItems(WheelCategory inputsCat, PackageManager pm) {
        boolean addedHdmi = false;
        try {
            TvInputManager tim = (TvInputManager) activity.getSystemService(Context.TV_INPUT_SERVICE);
            if (tim != null) {
                int hdmiNum = 1;
                for (TvInputInfo info : tim.getTvInputList()) {
                    if (info.isPassthroughInput()) {
                        CharSequence customLabel = info.loadCustomLabel(activity);
                        CharSequence baseLabel = info.loadLabel(activity);
                        String name = customLabel != null && customLabel.length() > 0
                                ? customLabel.toString()
                                : (baseLabel != null ? baseLabel.toString() : ("HDMI " + hdmiNum));
                        String upper = name.toUpperCase(Locale.ROOT);
                        String icon = hdmiNum == 4 ? "earc" : ("hdmi" + Math.min(4, hdmiNum));
                        Uri uri = TvContract.buildChannelUriForPassthroughInput(info.getId());
                        Intent viewInput = new Intent(Intent.ACTION_VIEW, uri);
                        inputsCat.items.add(new WheelItem(
                                info.getId(), upper, name, upper,
                                "Switch directly to " + name + " input source",
                                icon, viewInput, null));
                        hdmiNum++;
                        addedHdmi = true;
                    }
                }
            }
        } catch (Exception ignored) {
        }

        if (!addedHdmi) {
            for (int i = 1; i <= 4; i++) {
                String lbl = i == 4 ? "HDMI 4 eARC" : ("HDMI " + i);
                Intent fallback = getBestLaunchIntent(pm, "com.tcl.tv");
                inputsCat.items.add(new WheelItem(
                        "hdmi" + i, lbl, lbl, lbl,
                        "Switch to " + lbl + " high-speed input port",
                        i == 4 ? "earc" : ("hdmi" + i), fallback, "com.tcl.tv"));
            }
        }

        Intent usbMedia = getBestLaunchIntent(pm, "com.tcl.ui_mediaCenter");
        inputsCat.items.add(new WheelItem(
                "usb_media", "USB MEDIA", "USB", "USB MEDIA DRIVE",
                "Browse videos, photos & music on connected USB storage",
                "usb", usbMedia != null ? usbMedia : getBestLaunchIntent(pm, "com.tcl.tv"), "com.tcl.ui_mediaCenter"));
    }

    private WheelCategory getCurrentCategory() {
        return categories.get(leftIndex);
    }

    private int getCurrentItemIndex() {
        int idx = rightIndices[leftIndex];
        int size = getCurrentCategory().items.size();
        if (size == 0) return 0;
        return ((idx % size) + size) % size;
    }

    private WheelItem getCurrentItem() {
        List<WheelItem> list = getCurrentCategory().items;
        if (list.isEmpty()) {
            return new WheelItem("empty", "EMPTY", "Empty", "NO ITEMS", "", "apps", null, null);
        }
        return list.get(getCurrentItemIndex());
    }

    private float shortestDelta(float from, float to, int len) {
        if (len <= 0) return 0f;
        float diff = (to - from) % len;
        if (diff > len / 2f) diff -= len;
        if (diff < -len / 2f) diff += len;
        return diff;
    }

    @Override
    public boolean onKeyDown(int keyCode, KeyEvent event) {
        // If TV is off or in CRT collapse, any key wakes the TV and triggers the smooth switch-on animation!
        if (!isTvPoweredOn || isCrtPoweringOff) {
            triggerTvPowerOn();
            playSoundEffect(SoundEffectConstants.CLICK);
            return true;
        }
        if (keyCode == KeyEvent.KEYCODE_SLEEP || keyCode == KeyEvent.KEYCODE_SOFT_SLEEP
                || keyCode == KeyEvent.KEYCODE_TV_POWER || keyCode == KeyEvent.KEYCODE_POWER) {
            startCrtPowerOff();
            return true;
        }
        switch (keyCode) {
            case KeyEvent.KEYCODE_DPAD_UP:
                topDeckWheelTarget -= 1f;
                if (!rightWheelActive) {
                    int len = categories.size();
                    leftIndex = (leftIndex - 1 + len) % len;
                    rightScroll = rightIndices[leftIndex];
                } else {
                    int len = getCurrentCategory().items.size();
                    if (len > 0) {
                        rightIndices[leftIndex] = (rightIndices[leftIndex] - 1 + len) % len;
                    }
                }
                isStartupClockMode = "clock".equals(getCurrentItem().iconType);
                heroPopProgress = 0.0f;
                playSoundEffect(SoundEffectConstants.NAVIGATION_UP);
                return true;

            case KeyEvent.KEYCODE_DPAD_DOWN:
                topDeckWheelTarget += 1f;
                if (!rightWheelActive) {
                    int len = categories.size();
                    leftIndex = (leftIndex + 1) % len;
                    rightScroll = rightIndices[leftIndex];
                } else {
                    int len = getCurrentCategory().items.size();
                    if (len > 0) {
                        rightIndices[leftIndex] = (rightIndices[leftIndex] + 1) % len;
                    }
                }
                isStartupClockMode = "clock".equals(getCurrentItem().iconType);
                heroPopProgress = 0.0f;
                playSoundEffect(SoundEffectConstants.NAVIGATION_DOWN);
                return true;

            case KeyEvent.KEYCODE_DPAD_LEFT:
                if ("clock".equals(getCurrentItem().iconType) || isStartupClockMode) {
                    return true;
                }
                rightWheelActive = false;
                playSoundEffect(SoundEffectConstants.NAVIGATION_LEFT);
                return true;

            case KeyEvent.KEYCODE_DPAD_RIGHT:
                if ("clock".equals(getCurrentItem().iconType) || isStartupClockMode) {
                    for (int i = 0; i < categories.size(); i++) {
                        if ("apps".equals(categories.get(i).id)) {
                            leftIndex = i;
                            break;
                        }
                    }
                    rightWheelActive = true;
                    isStartupClockMode = false;
                    heroPopProgress = 0.0f;
                    topDeckWheelTarget += 1.0f;
                    playSoundEffect(SoundEffectConstants.NAVIGATION_RIGHT);
                    invalidate();
                    return true;
                }
                rightWheelActive = true;
                playSoundEffect(SoundEffectConstants.NAVIGATION_RIGHT);
                return true;

            case KeyEvent.KEYCODE_DPAD_CENTER:
            case KeyEvent.KEYCODE_ENTER:
            case KeyEvent.KEYCODE_NUMPAD_ENTER:
                playSoundEffect(SoundEffectConstants.CLICK);
                if ("clock".equals(getCurrentItem().iconType) || isStartupClockMode) {
                    // Clicking OK/Enter on the Home Clock switches directly into the Apps wheel!
                    for (int i = 0; i < categories.size(); i++) {
                        if ("apps".equals(categories.get(i).id)) {
                            leftIndex = i;
                            break;
                        }
                    }
                    rightWheelActive = true;
                    isStartupClockMode = false;
                    heroPopProgress = 0.0f;
                    topDeckWheelTarget += 1.0f;
                    invalidate();
                    return true;
                }
                if (!rightWheelActive) {
                    rightWheelActive = true;
                    return true;
                }
                launchSelectedItem();
                return true;

            case KeyEvent.KEYCODE_BACK:
                if (rightWheelActive) {
                    rightWheelActive = false;
                    playSoundEffect(SoundEffectConstants.NAVIGATION_LEFT);
                    return true;
                } else if (!isStartupClockMode) {
                    // Smoothly glide back to Startup Clock Mode
                    leftIndex = 0;
                    rightIndices[0] = 0;
                    rightScroll = 0f;
                    isStartupClockMode = true;
                    playSoundEffect(SoundEffectConstants.NAVIGATION_UP);
                    return true;
                }
                return true;
        }
        return super.onKeyDown(keyCode, event);
    }

    private void launchSelectedItem() {
        WheelItem item = getCurrentItem();
        if ("screen_saver".equals(item.id)) {
            // Trigger CRT TV power off into pitch-black Mini LED standby!
            startCrtPowerOff();
            return;
        }
        if ("ambient_clock".equals(item.id)) {
            leftIndex = 0;
            rightIndices[0] = 0;
            rightScroll = 0f;
            rightWheelActive = false;
            isStartupClockMode = true;
            return;
        }
        if (item.launchIntent != null) {
            try {
                Intent i = new Intent(item.launchIntent);
                i.addFlags(Intent.FLAG_ACTIVITY_NEW_TASK);
                activity.startActivity(i);
            } catch (Exception e) {
                try {
                    activity.startActivity(new Intent(Settings.ACTION_SETTINGS).addFlags(Intent.FLAG_ACTIVITY_NEW_TASK));
                } catch (Exception ignored) {
                }
            }
        }
    }

    private void updateClockCacheIfNeeded() {
        long now = System.currentTimeMillis();
        if (now - lastTimeUpdateMs >= 1000L || cachedTimeStr.isEmpty()) {
            lastTimeUpdateMs = now;
            Date d = new Date(now);
            cachedTimeStr = timeFormat.format(d);
            cachedDateStr = dateFormat.format(d).toUpperCase(Locale.US);
            cachedTzOffsetMs = java.util.TimeZone.getDefault().getOffset(now);
        }
    }

    @Override
    protected void onDraw(Canvas canvas) {
        super.onDraw(canvas);

        long nowNanos = System.nanoTime();
        float dt = (lastFrameNanos == 0L) ? 0.016f : ((nowNanos - lastFrameNanos) * 1e-9f);
        lastFrameNanos = nowNanos;
        if (dt < 0.004f) dt = 0.004f;
        if (dt > 0.050f) dt = 0.050f;
        animTimeSec += dt;

        updateClockCacheIfNeeded();

        float w = getWidth();
        float h = getHeight();
        if (w <= 0 || h <= 0) return;

        canvas.save();
        canvas.scale(w / 1920f, h / 1080f);

        // 1. Critically-damped smooth spring for Clock Mode <-> Expanded Wheels (broad, fluid motion)
        float targetStartup = isStartupClockMode ? 1.0f : 0.0f;
        float stiffness = 24.0f;
        float damping = 8.8f;
        float force = (targetStartup - startupLerp) * stiffness - startupVelocity * damping;
        startupVelocity += force * dt;
        startupLerp += startupVelocity * dt;
        if (Math.abs(targetStartup - startupLerp) < 0.001f && Math.abs(startupVelocity) < 0.005f) {
            startupLerp = targetStartup;
            startupVelocity = 0f;
        }

        // 2. Smooth, broad exponential glide for Left & Right Wheel rotation + Top Endurance Deck
        float wheelLerpFactor = 1.0f - (float) Math.exp(-8.5f * dt);
        topDeckWheelScroll += (topDeckWheelTarget - topDeckWheelScroll) * wheelLerpFactor;

        int lLen = categories.size();
        float lDelta = shortestDelta(leftScroll, leftIndex, lLen);
        leftScroll = (leftScroll + lDelta * wheelLerpFactor + lLen) % lLen;

        List<WheelItem> rItems = getCurrentCategory().items;
        int rLen = Math.max(1, rItems.size());
        int rTarget = getCurrentItemIndex();
        float rDelta = shortestDelta(rightScroll, rTarget, rLen);
        rightScroll = (rightScroll + rDelta * wheelLerpFactor + rLen) % rLen;

        // 3. Smooth Center Stage Hero Pop/Fade animation when active item changes
        WheelItem curItem = getCurrentItem();
        if (!curItem.id.equals(lastHeroItemId)) {
            lastHeroItemId = curItem.id;
            heroPopProgress = 0.0f;
        }
        heroPopProgress = Math.min(1.0f, heroPopProgress + dt * 3.8f);

        // 4. TV Power State Handling:
        // If TV is off and not in CRT power-off animation, draw pure black and return immediately
        if (!isTvPoweredOn && !isCrtPoweringOff) {
            canvas.drawColor(Color.BLACK);
            canvas.restore();
            return;
        }

        // Animate CRT Power OFF (takes ~420ms: vertical collapse -> horizontal single-point collapse -> wink out)
        if (isCrtPoweringOff) {
            crtOffProgress = Math.min(1.0f, crtOffProgress + dt * 2.4f);
            if (crtOffProgress >= 1.0f) {
                isCrtPoweringOff = false;
                isTvPoweredOn = false;
                canvas.drawColor(Color.BLACK);
                canvas.restore();
                HomeKeyService.goToSleep();
                return;
            }
        }

        // Animate Switch ON (wheels enter from either ends, black hole appears from nowhere)
        if (isTvPoweredOn && !isCrtPoweringOff) {
            if (enterProgress < 1.0f) {
                enterProgress = Math.min(1.0f, enterProgress + dt * 1.35f);
            }
        }

        if (isCrtPoweringOff) {
            drawCrtPowerOff(canvas, curItem, dt);
        } else {
            drawNormalUi(canvas, curItem, dt);
        }

        canvas.restore();
        postInvalidateOnAnimation();
    }

    private void drawNormalUi(Canvas canvas, WheelItem curItem, float dt) {
        float enterT = Math.min(1.0f, Math.max(0f, enterProgress));
        float invE = 1.0f - enterT;
        float easeEnter = 1.0f - invE * invE * invE;

        // 1. Pure Pitch-Black Cosmic Void background
        canvas.drawColor(Color.rgb(2, 2, 4));

        // 2. Black Hole appears from nowhere! Scale grows from 0.05 -> 1.0, alpha 0.0 -> 1.0
        float bhScale = 0.05f + 0.95f * easeEnter;
        float bhAlpha = easeEnter;

        canvas.save();
        canvas.translate(960f, 516f);
        canvas.scale(bhScale, bhScale);
        canvas.translate(-960f, -516f);
        drawWallpaperAndSparks(canvas, dt, bhAlpha);
        drawCenterStage(canvas, curItem, bhAlpha);
        canvas.restore();

        // 3. Both Wheels enter from either ends!
        int rTarget = getCurrentItemIndex();
        drawWheel(canvas, true, leftScroll, leftIndex, !rightWheelActive, easeEnter);
        drawWheel(canvas, false, rightScroll, rTarget, rightWheelActive, easeEnter);

        // 4. Top bar fades in as wheels settle
        float topBarAlpha = Math.max(0f, (easeEnter - 0.35f) / 0.65f);
        if (topBarAlpha > 0.01f) {
            drawTopBar(canvas, topBarAlpha);
        }
    }

    private void drawCrtPowerOff(Canvas canvas, WheelItem curItem, float dt) {
        float p = crtOffProgress;

        if (p <= 0.55f) {
            // Phase 1: Vertical Deflection Collapse (0.0 -> 0.55)
            // Screen collapses vertically into a bright horizontal beam along y = 540
            float vNorm = p / 0.55f;
            float easeV = vNorm * vNorm;
            float scaleY = Math.max(0.003f, 1.0f - easeV);
            float scaleX = 1.0f;

            canvas.save();
            canvas.translate(960f, 540f);
            canvas.scale(scaleX, scaleY);
            canvas.translate(-960f, -540f);
            drawNormalUi(canvas, curItem, dt);
            canvas.restore();

            // CRT horizontal phosphor beam flare across the center line
            float beamIntensity = 0.4f + 0.6f * easeV;
            float beamWidth = 2.5f + 7.5f * easeV;

            crtGlowPaint.setColor(Color.argb(Math.round(beamIntensity * 160f), 245, 250, 255));
            crtGlowPaint.setStrokeWidth(beamWidth * 2.6f);
            canvas.drawLine(0f, 540f, 1920f, 540f, crtGlowPaint);

            crtLinePaint.setColor(Color.argb(Math.round(beamIntensity * 255f), 255, 255, 255));
            crtLinePaint.setStrokeWidth(beamWidth);
            canvas.drawLine(0f, 540f, 1920f, 540f, crtLinePaint);

        } else if (p <= 0.88f) {
            // Phase 2: Horizontal Deflection Collapse into Single Point (0.55 -> 0.88)
            // The bright horizontal beam contracts horizontally into the center point (960, 540)
            float hNorm = (p - 0.55f) / 0.33f;
            float easeH = hNorm * hNorm;
            float scaleX = Math.max(0.002f, 1.0f - easeH);
            float scaleY = 0.003f;

            canvas.save();
            canvas.translate(960f, 540f);
            canvas.scale(scaleX, scaleY);
            canvas.translate(-960f, -540f);
            drawNormalUi(canvas, curItem, dt);
            canvas.restore();

            float halfW = 960f * (1.0f - easeH);
            float glowW = 10.0f * (1.0f - hNorm * 0.4f);

            crtGlowPaint.setColor(Color.argb(210, 240, 248, 255));
            crtGlowPaint.setStrokeWidth(glowW);
            canvas.drawLine(960f - halfW, 540f, 960f + halfW, 540f, crtGlowPaint);

            crtLinePaint.setColor(Color.WHITE);
            crtLinePaint.setStrokeWidth(3.5f);
            canvas.drawLine(960f - halfW, 540f, 960f + halfW, 540f, crtLinePaint);

        } else {
            // Phase 3: Single Phosphor Point Afterglow & Wink Out (0.88 -> 1.0)
            // Everything has collapsed into a single glowing dot that dims and winks out
            float dotNorm = (p - 0.88f) / 0.12f;
            float dotR = 7.5f * (1.0f - dotNorm);
            int alpha = Math.max(0, Math.min(255, Math.round(255f * (1.0f - dotNorm))));

            crtGlowPaint.setColor(Color.argb(Math.round(alpha * 0.75f), 240, 248, 255));
            canvas.drawCircle(960f, 540f, dotR * 2.8f, crtGlowPaint);

            crtLinePaint.setStyle(Paint.Style.FILL);
            crtLinePaint.setColor(Color.argb(alpha, 255, 255, 255));
            canvas.drawCircle(960f, 540f, dotR, crtLinePaint);
            crtLinePaint.setStyle(Paint.Style.STROKE);
        }
    }

    private void drawQuietCosmosMicroDetails(Canvas canvas, float alphaScale) {
        if (alphaScale <= 0.01f) return;

        // 1. Crisp Native 1080p Pinprick Starfield (breathing ultra-slowly over 7-14s, zero blur!)
        paint.reset();
        paint.setAntiAlias(true);
        for (int i = 0; i < bgStars.size(); i++) {
            BgStar s = bgStars.get(i);
            float breath = 0.62f + 0.38f * (float) Math.sin((animTimeSec / s.period) * Math.PI * 2.0 + s.phase);
            int a = Math.min(255, Math.max(0, Math.round(s.baseAlpha * breath * alphaScale * 255f)));
            if (a <= 2) continue;

            paint.setStyle(Paint.Style.FILL);
            paint.setColor(Color.argb(a, s.r, s.g, s.b));
            canvas.drawCircle(s.x, s.y, s.size, paint);

            if (s.isGlint) {
                float arm = 7.5f + 3.5f * breath;
                paint.setStyle(Paint.Style.STROKE);
                paint.setStrokeWidth(0.95f);
                paint.setColor(Color.argb(Math.round(a * 0.55f), s.r, s.g, s.b));
                canvas.drawLine(s.x - arm, s.y, s.x + arm, s.y, paint);
                canvas.drawLine(s.x, s.y - arm, s.x, s.y + arm, paint);
            }
        }

        // 2. Minimalist Backlit Miller's Planet (upper-left, razor-sharp crescent illuminated by Gargantua)
        float millerAngle = (float) Math.toDegrees(Math.atan2(516f - 232f, 960f - 392f));
        drawCrescentPlanet(canvas, 392f, 232f, 34f, millerAngle, millerHaloGrad, millerLitGrad,
                Color.argb(Math.round(215 * alphaScale), 255, 224, 176), 1.5f, alphaScale);

        // 3. Distant Tiny Mann's Ice World (upper-right, backlit silver-blue crescent facing Gargantua)
        float mannAngle = (float) Math.toDegrees(Math.atan2(516f - 228f, 960f - 1522f));
        drawCrescentPlanet(canvas, 1522f, 228f, 13f, mannAngle, mannHaloGrad, mannLitGrad,
                Color.argb(Math.round(215 * alphaScale), 215, 234, 255), 1.1f, alphaScale);

        // 4. Rare, Refined Shooting Star (once every ~9 seconds across a distant corner)
        if (animTimeSec >= nextMeteorSec && !meteorActive) {
            int quad = ((int) animTimeSec) % 3;
            meteorSx = quad == 0 ? 260f : (quad == 1 ? 1420f : 1220f);
            meteorSy = quad == 0 ? 140f : (quad == 1 ? 130f : 860f);
            meteorVx = quad == 0 ? 440f : (quad == 1 ? -460f : 380f);
            meteorVy = quad == 0 ? 190f : (quad == 1 ? 210f : -160f);
            meteorStartSec = animTimeSec;
            meteorDur = 0.72f;
            meteorActive = true;
            nextMeteorSec = animTimeSec + 8.5f + (animTimeSec % 3.5f);
        }
        if (meteorActive) {
            float p = (animTimeSec - meteorStartSec) / meteorDur;
            if (p >= 1.0f || p < 0f) {
                meteorActive = false;
            } else {
                float fade = (float) Math.sin(p * Math.PI) * alphaScale;
                float hx = meteorSx + meteorVx * p;
                float hy = meteorSy + meteorVy * p;
                float tx = meteorSx + meteorVx * Math.max(0f, p - 0.22f);
                float ty = meteorSy + meteorVy * Math.max(0f, p - 0.22f);

                paint.reset();
                paint.setAntiAlias(true);
                paint.setStyle(Paint.Style.STROKE);
                paint.setStrokeCap(Paint.Cap.ROUND);
                paint.setStrokeWidth(1.6f);
                paint.setShader(new LinearGradient(
                        tx, ty, hx, hy,
                        new int[]{
                                Color.argb(0, 255, 226, 180),
                                Color.argb(Math.round(120 * fade), 255, 232, 192),
                                Color.argb(Math.round(245 * fade), 255, 252, 244)
                        },
                        new float[]{0f, 0.7f, 1f},
                        Shader.TileMode.CLAMP));
                canvas.drawLine(tx, ty, hx, hy, paint);
                paint.setShader(null);

                paint.setStyle(Paint.Style.FILL);
                paint.setColor(Color.argb(Math.round(245 * fade), 255, 255, 255));
                canvas.drawCircle(hx, hy, 1.8f, paint);
            }
        }
    }

    private void drawCrescentPlanet(Canvas canvas, float px, float py, float r, float lightDeg,
                                    RadialGradient haloGrad, RadialGradient litGrad,
                                    int rimColor, float rimStroke, float alphaScale) {
        canvas.save();
        canvas.translate(px, py);
        canvas.rotate(lightDeg);

        int alpha255 = Math.min(255, Math.max(0, Math.round(alphaScale * 255f)));

        // Subtle atmospheric halo on sunlit limb facing Gargantua
        if (haloGrad != null) {
            paint.reset();
            paint.setAntiAlias(true);
            paint.setStyle(Paint.Style.FILL);
            paint.setShader(haloGrad);
            paint.setAlpha(alpha255);
            canvas.drawCircle(0f, 0f, r * 1.5f, paint);
            paint.setShader(null);
        }

        // Clipped planet disc with pitch-black shadowed hemisphere + luminous backlit crescent
        canvas.save();
        path.reset();
        path.addCircle(0f, 0f, r, Path.Direction.CW);
        canvas.clipPath(path);

        if (litGrad != null) {
            paint.reset();
            paint.setAntiAlias(true);
            paint.setStyle(Paint.Style.FILL);
            paint.setShader(litGrad);
            paint.setAlpha(alpha255);
            canvas.drawRect(-r, -r, r, r, paint);
            paint.setShader(null);
        }

        paint.reset();
        paint.setAntiAlias(true);
        paint.setStyle(Paint.Style.FILL);
        paint.setColor(Color.BLACK);
        canvas.drawCircle(-r * 0.22f, 0f, r * 0.96f, paint);
        canvas.restore();

        // Crisp luminous rim arc along the sunlit edge
        paint.reset();
        paint.setAntiAlias(true);
        paint.setStyle(Paint.Style.STROKE);
        paint.setStrokeCap(Paint.Cap.ROUND);
        paint.setStrokeWidth(rimStroke);
        paint.setColor(rimColor);
        rectF.set(-r, -r, r, r);
        canvas.drawArc(rectF, -54f, 108f, false, paint);

        canvas.restore();
    }

    private void drawWallpaperAndSparks(Canvas canvas, float dt, float bhAlpha) {
        float cx = 960f;
        float cy = 516f;
        float eLerp = Math.max(0f, Math.min(1f, startupLerp));
        float topLerp = 1.0f - eLerp;

        // 1. Pure True OLED / Mini-LED Black Void (#000000) + Razor-Sharp Native 1080p Space Micro-Details
        canvas.drawColor(Color.BLACK);
        drawQuietCosmosMicroDetails(canvas, bhAlpha);

        // 2. Top-View Black Hole Ring (Apps screen & morph transition)
        if (topLerp > 0.005f && bhTopAlphaBitmap != null) {
            canvas.save();
            canvas.translate(cx, cy);
            float deg = (float) Math.toDegrees(animTimeSec * 0.08f * (0.35f + 0.65f * topLerp));
            canvas.rotate(deg);
            bitmapPaint.setAlpha(Math.min(255, Math.max(0, Math.round(topLerp * 255f * bhAlpha))));
            canvas.drawBitmap(bhTopAlphaBitmap, -cx, -cy, bitmapPaint);
            bitmapPaint.setAlpha(255);
            canvas.restore();
        }

        // 3. Razor-Sharp Cropped High-Res Gargantua (7.0s optical-flow golden bokeh, exact GPU additive crossfade)
        if (eLerp > 0.005f && bhFlowFrames[0] != null) {
            canvas.save();
            canvas.translate(cx, cy);
            float scaleX = 0.65f + 0.35f * eLerp;
            float scaleY = 0.96f + 0.04f * eLerp;
            canvas.scale(scaleX, scaleY);
            bhDstRect.set(BH_CROP_X - cx, BH_CROP_Y - cy, BH_CROP_X + BH_CROP_W - cx, BH_CROP_Y + BH_CROP_H - cy);

            float baseAlpha = eLerp * bhAlpha;
            if (bhFramesReady) {
                float pos = ((animTimeSec / BH_FLOW_LOOP_SEC) % 1.0f) * BH_FRAME_COUNT;
                if (pos < 0f) pos += BH_FRAME_COUNT;
                int i0 = ((int) Math.floor(pos)) % BH_FRAME_COUNT;
                int i1 = (i0 + 1) % BH_FRAME_COUNT;
                float frac = pos - (float) Math.floor(pos);

                Bitmap f0 = bhFlowFrames[i0] != null ? bhFlowFrames[i0] : bhFlowFrames[0];
                Bitmap f1 = bhFlowFrames[i1] != null ? bhFlowFrames[i1] : f0;

                if (f1 != f0 && frac > 0.005f) {
                    int a0 = Math.min(255, Math.max(0, Math.round((1.0f - frac) * baseAlpha * 255f)));
                    int a1 = Math.min(255, Math.max(0, Math.round(frac * baseAlpha * 255f)));
                    if (a0 > 0) {
                        bhAddPaint.setAlpha(a0);
                        canvas.drawBitmap(f0, null, bhDstRect, bhAddPaint);
                    }
                    if (a1 > 0) {
                        bhAddPaint.setAlpha(a1);
                        canvas.drawBitmap(f1, null, bhDstRect, bhAddPaint);
                    }
                } else {
                    bhAddPaint.setAlpha(Math.min(255, Math.max(0, Math.round(baseAlpha * 255f))));
                    canvas.drawBitmap(f0, null, bhDstRect, bhAddPaint);
                }
            } else {
                bhAddPaint.setAlpha(Math.min(255, Math.max(0, Math.round(baseAlpha * 255f))));
                canvas.drawBitmap(bhFlowFrames[0], null, bhDstRect, bhAddPaint);
            }
            bhAddPaint.setAlpha(255);
            canvas.restore();
        }

        // 4. Opaque True-Black Event Horizon Sphere (r = 209px)
        paint.reset();
        paint.setAntiAlias(true);
        paint.setStyle(Paint.Style.FILL);
        paint.setColor(Color.BLACK);
        canvas.drawCircle(cx, cy, 209f, paint);

        // 5. Angled (-22 deg) Equatorial Accretion Glow across the Event Horizon in Clock Mode
        if (eLerp > 0.02f && eqHorizonGradient != null) {
            canvas.save();
            path.reset();
            path.addCircle(cx, cy, 209f, Path.Direction.CW);
            canvas.clipPath(path);
            canvas.translate(cx, cy);
            canvas.rotate(-22f);
            paint.reset();
            paint.setAntiAlias(true);
            paint.setStyle(Paint.Style.FILL);
            paint.setShader(eqHorizonGradient);
            paint.setAlpha(Math.min(255, Math.round(eLerp * 255f * bhAlpha)));
            canvas.drawRect(-215f, -26f, 215f, 52f, paint);
            paint.setShader(null);
            canvas.restore();
        }

        // 7. Photorealistic Interstellar ENDURANCE Spacecraft:
        //    - On Home Screen: rotates continuously clockwise at a noticeable speed (0.62 rad/s) at (1410, 815)
        //      with a subtle warm pulsing docking navigation beacon.
        //    - When toggling Apps: seamlessly exits rotating clockwise to the right AND morphs/sweeps into the enlarged
        //      circular deck at the top center (960, -185, size 790x790), rotating in sync with the wheels!
        if (enduranceShipBitmap != null) {
            float appLerp = 1.0f - eLerp;
            float cwSpinRad = animTimeSec * 0.62f;

            // Phase A: Home foreground ship (1410, 815) -> exits rotating clockwise to the right as appLerp goes 0 -> 1
            float exitT = Math.max(0f, Math.min(1f, appLerp * 1.42f));
            if (exitT < 0.995f) {
                float easeIn = exitT * exitT;
                float shipCx = 1410f + easeIn * 640f;
                float shipCy = 815f - easeIn * 240f;
                float halfSz = (308f + easeIn * 180f) * 0.5f;
                float shipAlpha = Math.max(0f, 1.0f - (float) Math.pow(exitT, 1.6f)) * bhAlpha;

                canvas.save();
                canvas.translate(shipCx, shipCy);
                float rotDeg = (float) Math.toDegrees(cwSpinRad + easeIn * 2.2f);
                canvas.rotate(rotDeg);
                bitmapPaint.setAlpha(Math.min(255, Math.max(0, Math.round(shipAlpha * 255f))));
                rectF.set(-halfSz, -halfSz, halfSz, halfSz);
                canvas.drawBitmap(enduranceShipBitmap, null, rectF, bitmapPaint);
                bitmapPaint.setAlpha(255);

                // Subtle warm pulsing spacecraft navigation beacon on Endurance central hub
                if (shipBeaconGrad != null) {
                    float pulse = (float) Math.pow(0.5 + 0.5 * Math.sin(animTimeSec * 2.1), 3.0);
                    int bAlpha = Math.round(pulse * shipAlpha * 230f);
                    if (bAlpha > 8) {
                        paint.reset();
                        paint.setAntiAlias(true);
                        paint.setStyle(Paint.Style.FILL);
                        paint.setShader(shipBeaconGrad);
                        paint.setAlpha(bAlpha);
                        canvas.drawCircle(0f, 0f, 14f, paint);
                        paint.setShader(null);
                    }
                }
                canvas.restore();
            }

            // Phase B: Enlarged Circular Deck at Top Center (960, -185, size 790x790) -> sweeps in & rotates matching wheels!
            float enterT = Math.max(0f, Math.min(1f, (appLerp - 0.14f) / 0.86f));
            if (enterT > 0.005f) {
                float invE = 1.0f - enterT;
                float easeOut = 1.0f - invE * invE * invE;
                float topCx = 960f + (1.0f - easeOut) * 420f;
                float topCy = -185f - (1.0f - easeOut) * 310f;
                float topHalfSz = (500f + easeOut * 290f) * 0.5f;

                float wheelRotRad = -topDeckWheelScroll * 0.52f + animTimeSec * 0.08f;
                float deckRotDeg = (float) Math.toDegrees(cwSpinRad * (1.0f - easeOut) + wheelRotRad * easeOut);

                canvas.save();
                canvas.translate(topCx, topCy);
                canvas.rotate(deckRotDeg);
                bitmapPaint.setAlpha(Math.min(255, Math.max(0, Math.round(easeOut * 255f * bhAlpha))));
                rectF.set(-topHalfSz, -topHalfSz, topHalfSz, topHalfSz);
                canvas.drawBitmap(enduranceShipBitmap, null, rectF, bitmapPaint);
                canvas.restore();
            }
        }
    }

    private void drawWheel(Canvas canvas, boolean isLeft, float currentScroll, int selectedIndex, boolean isWheelActive, float easeEnter) {
        // Smooth cubic ease on startupLerp for broader, silkier wheel retraction/expansion
        float clampedLerp = Math.max(0f, Math.min(1.15f, startupLerp));
        float retractOffset = clampedLerp * 165f;
        float wheelScale = 1.0f - clampedLerp * 0.23f;

        // Positioned so wheels enter from either ends of the TV screen!
        // Offscreen left start: -720f (well outside left bezel 0)
        // Offscreen right start: 2640f (well outside right bezel 1920)
        float offscreenLeftCx = -720f;
        float offscreenRightCx = 2640f;
        float restingCx = isLeft ? (-72f - retractOffset) : (1920f + 72f + retractOffset);

        float baseCx = isLeft
                ? (offscreenLeftCx + (restingCx - offscreenLeftCx) * easeEnter)
                : (offscreenRightCx + (restingCx - offscreenRightCx) * easeEnter);
        float cy = 540f;

        // Single clean inner boundary (0 inner circles behind the Category/App hub title!)
        float rInner = 282f * wheelScale;
        float rOuter = 562f * wheelScale;
        float rRim = 612f * wheelScale;

        int alphaMul = Math.min(255, Math.max(0, Math.round((1.0f - clampedLerp * 0.28f) * 255f * easeEnter)));

        // 1. Soft Golden-Amber Gravitational Lensing Glow around the Wheel's Outer Rim
        glowPaint.reset();
        glowPaint.setAntiAlias(true);
        glowPaint.setStyle(Paint.Style.STROKE);
        glowPaint.setStrokeWidth(26f * wheelScale);
        glowPaint.setColor(Color.argb(Math.round(alphaMul * (isWheelActive ? 0.14f : 0.06f)), 255, 212, 155));
        canvas.drawCircle(baseCx, cy, rOuter + 14f * wheelScale, glowPaint);

        // 2. Deep Obsidian Event-Horizon Glass Annular Band (between rInner and rOuter)
        path.reset();
        path.setFillType(Path.FillType.EVEN_ODD);
        path.addCircle(baseCx, cy, rOuter, Path.Direction.CW);
        path.addCircle(baseCx, cy, rInner, Path.Direction.CW);
        paint.reset();
        paint.setAntiAlias(true);
        paint.setStyle(Paint.Style.FILL);
        paint.setColor(Color.argb(Math.round(alphaMul * 0.52f), 6, 7, 12));
        canvas.drawPath(path, paint);
        path.setFillType(Path.FillType.WINDING);

        // 3. Pure Pitch-Black Obsidian Inner Hub (NO inner circles behind Category/App hub title!)
        paint.setStyle(Paint.Style.FILL);
        paint.setColor(Color.argb(Math.round(alphaMul * 0.74f), 3, 4, 7));
        canvas.drawCircle(baseCx, cy, rInner, paint);

        // 4. Rotating Relativistic Photon-Ring Micro-Ticks along the outer rim (rRim)
        canvas.save();
        canvas.translate(baseCx, cy);
        float tickRotDeg = (float) Math.toDegrees((isLeft ? 1f : -1f) * (-currentScroll * 0.15f + animTimeSec * 0.02f));
        canvas.rotate(tickRotDeg);
        paint.setStyle(Paint.Style.STROKE);
        paint.setStrokeWidth(1.4f);
        paint.setColor(isWheelActive
                ? Color.argb(Math.round(alphaMul * 0.36f), 255, 224, 178)
                : Color.argb(Math.round(alphaMul * 0.16f), 220, 205, 185));
        for (int t = 0; t < 72; t++) {
            double a = (t / 72.0) * Math.PI * 2.0;
            boolean isMajor = (t % 6 == 0);
            float r1 = rOuter + (isMajor ? 10f : 16f) * wheelScale;
            float r2 = rOuter + 24f * wheelScale;
            canvas.drawLine(
                    (float) Math.cos(a) * r1, (float) Math.sin(a) * r1,
                    (float) Math.cos(a) * r2, (float) Math.sin(a) * r2,
                    paint);
        }
        canvas.restore();

        // 5. Crisp Golden-Champagne Photon Ring Borders on rOuter and rInner
        paint.setStyle(Paint.Style.STROKE);
        paint.setStrokeWidth(isWheelActive ? 2.0f : 1.3f);
        paint.setColor(isWheelActive
                ? Color.argb(Math.round(alphaMul * 0.46f), 255, 222, 172)
                : Color.argb(Math.round(alphaMul * 0.20f), 235, 215, 188));
        canvas.drawCircle(baseCx, cy, rOuter, paint);

        paint.setStrokeWidth(2.0f);
        paint.setColor(isWheelActive
                ? Color.argb(Math.round(alphaMul * 0.58f), 255, 226, 182)
                : Color.argb(Math.round(alphaMul * 0.28f), 235, 218, 192));
        canvas.drawCircle(baseCx, cy, rInner, paint);

        // 6. Draw Broader Wedge Slots around Center Slot 0 (y = 540)
        float slotStepAngle = 0.44f;
        int len = isLeft ? categories.size() : Math.max(1, getCurrentCategory().items.size());

        for (int slot = -3; slot <= 3; slot++) {
            float fract = currentScroll - Math.round(currentScroll);
            float visualSlot = slot - fract;
            float centerAngle = visualSlot * slotStepAngle;

            if (Math.abs(centerAngle) > 1.42f) continue;

            int itemIdx = ((Math.round(currentScroll) + slot) % len + len) % len;
            boolean isSelectedWedge = (slot == 0) && (Math.abs(fract) < 0.35f);

            float aStart = isLeft
                    ? (centerAngle - slotStepAngle * 0.5f)
                    : ((float) Math.PI - centerAngle - slotStepAngle * 0.5f);
            float aEnd = isLeft
                    ? (centerAngle + slotStepAngle * 0.5f)
                    : ((float) Math.PI - centerAngle + slotStepAngle * 0.5f);
            float aMid = (aStart + aEnd) * 0.5f;

            if (!isSelectedWedge) {
                paint.reset();
                paint.setAntiAlias(true);
                paint.setStyle(Paint.Style.STROKE);
                paint.setStrokeWidth(1.3f);
                paint.setColor(Color.argb(Math.round(alphaMul * 0.12f), 255, 224, 180));
                canvas.drawLine(
                        baseCx + (float) Math.cos(aStart) * rInner,
                        cy + (float) Math.sin(aStart) * rInner,
                        baseCx + (float) Math.cos(aStart) * rOuter,
                        cy + (float) Math.sin(aStart) * rOuter,
                        paint);

                float midR = (rInner + rOuter) * 0.5f;
                float ix = baseCx + (float) Math.cos(aMid) * midR;
                float iy = cy + (float) Math.sin(aMid) * midR - 6f * wheelScale;

                // Smooth distance fade so outer slots feel spacious & cinematic
                float distFade = Math.max(0.35f, 1.0f - Math.abs(visualSlot) * 0.22f);
                int slotAlpha = Math.round(alphaMul * distFade);

                String iconType = isLeft ? categories.get(itemIdx).iconType : getCurrentCategory().items.get(itemIdx).iconType;
                String shortLbl = isLeft ? categories.get(itemIdx).shortLabel : getCurrentCategory().items.get(itemIdx).shortLabel;
                drawLogo(canvas, iconType, ix, iy, 29f * wheelScale, false, shortLbl, slotAlpha);
            }
        }

        // 7. Selected Center Wedge styled like an illuminated Photon-Ring Sector at Slot 0 (y = 540)
        float aMid = isLeft ? 0f : (float) Math.PI;
        float halfDeg = (float) Math.toDegrees(slotStepAngle * 0.52f);
        float startDeg = isLeft ? -halfDeg : (180f - halfDeg);
        float sweepDeg = halfDeg * 2f;

        float wInner = rInner - 6f * wheelScale;
        float wOuter = rOuter + 18f * wheelScale;

        path.reset();
        rectF.set(baseCx - wOuter, cy - wOuter, baseCx + wOuter, cy + wOuter);
        path.arcTo(rectF, startDeg, sweepDeg);
        rectF.set(baseCx - wInner, cy - wInner, baseCx + wInner, cy + wInner);
        path.arcTo(rectF, startDeg + sweepDeg, -sweepDeg);
        path.close();

        paint.reset();
        paint.setAntiAlias(true);
        paint.setStyle(Paint.Style.FILL);
        paint.setColor(isWheelActive
                ? Color.argb(Math.round(alphaMul * 0.58f), 46, 35, 22)
                : Color.argb(Math.round(alphaMul * 0.38f), 28, 22, 16));
        canvas.drawPath(path, paint);

        paint.setStyle(Paint.Style.STROKE);
        paint.setStrokeWidth(isWheelActive ? 2.6f : 1.6f);
        paint.setColor(isWheelActive
                ? Color.argb(Math.round(alphaMul * 0.94f), 255, 228, 182)
                : Color.argb(Math.round(alphaMul * 0.45f), 235, 215, 185));
        canvas.drawPath(path, paint);

        // Selected Wedge Logo + Outfit Label
        String activeIcon = isLeft ? categories.get(selectedIndex).iconType : getCurrentItem().iconType;
        String activeLabel = isLeft ? categories.get(selectedIndex).label : getCurrentItem().label;

        float textR = (wInner + wOuter) * 0.5f;
        float tx = baseCx + (float) Math.cos(aMid) * textR;
        drawLogo(canvas, activeIcon, tx, cy - 22f * wheelScale, 26f * wheelScale, false, "", alphaMul);

        textPaint.reset();
        textPaint.setAntiAlias(true);
        textPaint.setTypeface(brushTypeface);
        textPaint.setLetterSpacing(0.06f);
        textPaint.setTextSize(20f * wheelScale);
        textPaint.setTextAlign(Paint.Align.CENTER);
        textPaint.setColor(Color.argb(alphaMul, 255, 248, 238));
        canvas.drawText(activeLabel, tx, cy + 32f * wheelScale, textPaint);
        textPaint.setLetterSpacing(0f);

        // 8. Clean Minimalist Hub Title (0 inner circles behind it, matching warm golden-champagne accent!)
        float hubTextX = isLeft
                ? (baseCx + rInner * 0.54f)
                : (baseCx - rInner * 0.54f);
        if (hubTextX > 45f && hubTextX < 1875f) {
            String hubHeader = isLeft ? "CATEGORY" : getCurrentCategory().label;
            String hubTitle = isLeft ? getCurrentCategory().label : getCurrentItem().shortLabel.toUpperCase(Locale.ROOT);

            // Small subtle overline label
            textPaint.reset();
            textPaint.setAntiAlias(true);
            textPaint.setTypeface(sansTypeface);
            textPaint.setTextSize(11.5f * wheelScale);
            textPaint.setLetterSpacing(0.15f);
            textPaint.setTextAlign(Paint.Align.CENTER);
            textPaint.setColor(Color.argb(Math.round(alphaMul * 0.72f), 235, 215, 185));
            canvas.drawText(hubHeader, hubTextX, cy - 16f * wheelScale, textPaint);
            textPaint.setLetterSpacing(0f);

            // Main Outfit Title in the center of the wheel hub
            textPaint.reset();
            textPaint.setAntiAlias(true);
            textPaint.setTypeface(brushTypeface);
            textPaint.setLetterSpacing(0.06f);
            textPaint.setTextSize(21.5f * wheelScale);
            textPaint.setTextAlign(Paint.Align.CENTER);
            textPaint.setColor(Color.argb(alphaMul, 252, 248, 242));
            canvas.drawText(hubTitle, hubTextX, cy + 11f * wheelScale, textPaint);
            textPaint.setLetterSpacing(0f);

            // Warm golden-champagne underline inside the wheel hub
            float lineHalfW = 40f * wheelScale;
            paint.reset();
            paint.setAntiAlias(true);
            paint.setStyle(Paint.Style.STROKE);
            paint.setStrokeWidth(2.2f * wheelScale);
            paint.setStrokeCap(Paint.Cap.ROUND);
            paint.setColor(isWheelActive
                    ? Color.argb(Math.round(alphaMul * 0.90f), 255, 218, 162)
                    : Color.argb(Math.round(alphaMul * 0.42f), 225, 205, 175));
            canvas.drawLine(hubTextX - lineHalfW, cy + 23f * wheelScale, hubTextX + lineHalfW, cy + 23f * wheelScale, paint);
        }
    }

    private void drawCenterStage(Canvas canvas, WheelItem item, float bhAlpha) {
        float cx = 960f;
        float bhCy = 516f;
        boolean isClockItem = "clock".equals(item.iconType);

        // Cubic ease-out for item switch animation (broad, smooth entrance)
        float inv = 1.0f - heroPopProgress;
        float easeOut = 1.0f - inv * inv * inv;
        float popScale = isClockItem ? 1.0f : (0.86f + 0.14f * easeOut);
        int baseAlpha = isClockItem ? 255 : Math.min(255, Math.round(75f + 180f * easeOut));
        int heroAlpha = Math.min(255, Math.max(0, Math.round(baseAlpha * bhAlpha)));
        float ySlide = isClockItem ? 0f : ((1.0f - easeOut) * 14f);

        // Notice: The Clock NEVER shrinks! Its outerR = 220.83f * 0.96f = 212f matches the Black Hole's photon ring at (960, 516)!
        float heroSize = isClockItem ? 220.83f : (148f * popScale);
        float cy = isClockItem ? bhCy : (bhCy + ySlide * 0.4f);

        if (isClockItem) {
            // Top Welcome Heading above the Black Hole
            textPaint.reset();
            textPaint.setAntiAlias(true);
            textPaint.setTypeface(brushTypeface);
            textPaint.setLetterSpacing(0.12f);
            textPaint.setTextSize(38f);
            textPaint.setTextAlign(Paint.Align.CENTER);
            textPaint.setColor(Color.argb(Math.round(245f * bhAlpha), 250, 246, 240));
            canvas.drawText("WELCOME, THIS IS ADAM'S VISION", cx, 118f, textPaint);
            textPaint.setLetterSpacing(0f);

            paint.reset();
            paint.setAntiAlias(true);
            paint.setStyle(Paint.Style.FILL);
            paint.setColor(Color.argb(Math.round(180f * bhAlpha), 255, 218, 168));
            rectF.set(cx - 210f, 144f, cx + 210f, 148f);
            canvas.drawOval(rectF, paint);
        }

        // 1. Center Hero Logo or Full-Size Black Hole Clock
        drawLogo(canvas, item.iconType, cx, cy, heroSize, true, "", heroAlpha);

        if (!isClockItem) {
            // 2. Line 1: Minimalist Outfit Geometric Title lowered to y = 928f (pure pitch-black space below the Black Hole ring!)
            textPaint.reset();
            textPaint.setAntiAlias(true);
            textPaint.setTypeface(brushTypeface);
            textPaint.setLetterSpacing(0.08f);
            textPaint.setTextSize(48f);
            textPaint.setTextAlign(Paint.Align.CENTER);
            textPaint.setColor(Color.argb(heroAlpha, 252, 248, 242));
            canvas.drawText(item.title, cx, 928f + ySlide * 0.4f, textPaint);
            textPaint.setLetterSpacing(0f);

            // Warm Golden-Champagne Underline
            float strokeW = Math.max(240f, item.title.length() * 25f) * (0.6f + 0.4f * easeOut);
            paint.reset();
            paint.setAntiAlias(true);
            paint.setStyle(Paint.Style.FILL);
            paint.setColor(Color.argb(Math.round(heroAlpha * 0.78f), 255, 218, 168));
            rectF.set(cx - strokeW * 0.5f, 955f + ySlide * 0.4f, cx + strokeW * 0.5f, 959f + ySlide * 0.4f);
            canvas.drawOval(rectF, paint);

            // 3. Line 2: Small Subtitle Description below the underline
            textPaint.reset();
            textPaint.setAntiAlias(true);
            textPaint.setTypeface(sansTypeface);
            textPaint.setTextSize(23f);
            textPaint.setTextAlign(Paint.Align.CENTER);
            textPaint.setColor(Color.argb(Math.round(heroAlpha * 0.90f), 232, 224, 212));
            canvas.drawText(item.desc, cx, 996f + ySlide * 0.4f, textPaint);
        }
    }

    private void drawTopBar(Canvas canvas, float topBarAlpha) {
        int aText = Math.min(255, Math.round(230f * topBarAlpha));
        textPaint.reset();
        textPaint.setAntiAlias(true);
        textPaint.setTypeface(brushTypeface);
        textPaint.setTextSize(24f);
        textPaint.setColor(Color.argb(aText, 245, 238, 228));
        textPaint.setTextAlign(Paint.Align.RIGHT);
        canvas.drawText(cachedTimeStr, 1720f, 62f, textPaint);

        paint.reset();
        paint.setAntiAlias(true);
        paint.setStyle(Paint.Style.STROKE);
        paint.setStrokeWidth(2.4f);
        paint.setStrokeCap(Paint.Cap.ROUND);
        paint.setColor(Color.argb(aText, 245, 238, 228));
        textPaint.setTextAlign(Paint.Align.RIGHT);
        canvas.drawText(cachedTimeStr, 1720f, 62f, textPaint);

        paint.reset();
        paint.setAntiAlias(true);
        paint.setStyle(Paint.Style.STROKE);
        paint.setStrokeWidth(2.4f);
        paint.setStrokeCap(Paint.Cap.ROUND);
        paint.setColor(Color.argb(230, 245, 238, 228));

        float wx = 1765f, wy = 62f;
        int[] radii = new int[]{6, 12, 18};
        for (int r : radii) {
            rectF.set(wx - r, wy - r, wx + r, wy + r);
            canvas.drawArc(rectF, -135f, 90f, false, paint);
        }
        paint.setStyle(Paint.Style.FILL);
        canvas.drawCircle(wx, wy, 2.2f, paint);

        float ux = 1825f, uy = 54f;
        paint.setStyle(Paint.Style.STROKE);
        canvas.drawCircle(ux, uy, 17f, paint);
        paint.setStyle(Paint.Style.FILL);
        canvas.drawCircle(ux, uy - 4f, 5.5f, paint);
        rectF.set(ux - 10f, uy + 4f, ux + 10f, uy + 24f);
        canvas.drawArc(rectF, -155f, 130f, false, paint);
    }

    private void drawLogo(Canvas canvas, String type, float x, float y, float s,
                          boolean isHero, String smallCaption, int alpha) {
        canvas.save();
        canvas.translate(x, y);

        paint.reset();
        paint.setAntiAlias(true);
        paint.setStyle(Paint.Style.STROKE);
        paint.setStrokeWidth(isHero ? 6.0f : 2.5f);
        paint.setStrokeCap(Paint.Cap.ROUND);
        paint.setStrokeJoin(Paint.Join.ROUND);
        int col = Color.argb(alpha, 248, 246, 242);
        paint.setColor(col);

        switch (type) {
            case "clock": {
                if (isHero) {
                    // outerR = 212f matches the Black Hole's inner photon ring at (960, 564) pixel-for-pixel!
                    float outerR = s * 0.96f;

                    paint.setStyle(Paint.Style.STROKE);
                    paint.setStrokeWidth(1.8f);
                    paint.setColor(Color.argb(Math.round(alpha * 0.42f), 255, 232, 195));
                    canvas.drawCircle(0f, 0f, outerR, paint);

                    // 60 hour/minute ticks inside the Black Hole event horizon
                    for (int m = 0; m < 60; m++) {
                        double ang = (m / 60.0) * Math.PI * 2.0 - Math.PI / 2.0;
                        boolean isHr = (m % 5 == 0);
                        float r1 = isHr ? outerR * 0.885f : outerR * 0.925f;
                        float r2 = outerR * 0.968f;
                        paint.setStrokeWidth(isHr ? 3.0f : 1.2f);
                        paint.setColor(isHr
                                ? Color.argb(Math.round(alpha * 0.92f), 255, 244, 228)
                                : Color.argb(Math.round(alpha * 0.38f), 230, 215, 195));
                        canvas.drawLine(
                                (float) Math.cos(ang) * r1, (float) Math.sin(ang) * r1,
                                (float) Math.cos(ang) * r2, (float) Math.sin(ang) * r2,
                                paint);
                    }

                    // 1 to 12 Numbers in Outfit Font
                    float numR = outerR * 0.74f;
                    textPaint.reset();
                    textPaint.setAntiAlias(true);
                    textPaint.setTypeface(brushTypeface);
                    textPaint.setTextSize(s * 0.165f);
                    textPaint.setTextAlign(Paint.Align.CENTER);
                    textPaint.setColor(Color.argb(Math.round(alpha * 0.96f), 250, 246, 240));
                    Paint.FontMetrics fm = textPaint.getFontMetrics();
                    float textOffset = -(fm.ascent + fm.descent) * 0.5f;

                    for (int n = 1; n <= 12; n++) {
                        double ang = (n / 12.0) * Math.PI * 2.0 - Math.PI / 2.0;
                        float nx = (float) Math.cos(ang) * numR;
                        float ny = (float) Math.sin(ang) * numR + textOffset;
                        canvas.drawText(String.valueOf(n), nx, ny, textPaint);
                    }

                    // Clean, balanced Date + Month Readout in upper half of dial using matching Outfit Font
                    textPaint.reset();
                    textPaint.setAntiAlias(true);
                    textPaint.setTypeface(brushTypeface);
                    textPaint.setLetterSpacing(0f);
                    textPaint.setTextSize(s * 0.084f);
                    textPaint.setTextAlign(Paint.Align.CENTER);
                    textPaint.setColor(Color.argb(Math.round(alpha * 0.88f), 235, 225, 212));
                    canvas.drawText(cachedDateStr, 0f, -outerR * 0.31f, textPaint);

                    // Digital Time Readout inside lower half of clock
                    textPaint.reset();
                    textPaint.setAntiAlias(true);
                    textPaint.setTypeface(brushTypeface);
                    textPaint.setTextSize(s * 0.132f);
                    textPaint.setTextAlign(Paint.Align.CENTER);
                    textPaint.setColor(Color.argb(Math.round(alpha * 0.95f), 255, 220, 168));
                    canvas.drawText(cachedTimeStr, 0f, outerR * 0.37f, textPaint);

                    // 100% Continuous, flicker-free sweep hands derived directly from wall-clock milliseconds
                    long localMs = System.currentTimeMillis() + cachedTzOffsetMs;
                    float sec = ((localMs % 60000L) + 60000L) % 60000L / 1000.0f;
                    float min = (((localMs / 60000L) % 60L + 60L) % 60L) + sec / 60.0f;
                    float hr = (((localMs / 3600000L) % 12L + 12L) % 12L) + min / 60.0f;

                    double hrAng = (hr / 12.0) * Math.PI * 2.0 - Math.PI / 2.0;
                    double minAng = (min / 60.0) * Math.PI * 2.0 - Math.PI / 2.0;
                    double secAng = (sec / 60.0) * Math.PI * 2.0 - Math.PI / 2.0;

                    paint.setColor(Color.argb(alpha, 250, 248, 245));
                    paint.setStrokeWidth(7.0f);
                    canvas.drawLine(
                            -(float) Math.cos(hrAng) * s * 0.08f, -(float) Math.sin(hrAng) * s * 0.08f,
                            (float) Math.cos(hrAng) * outerR * 0.45f, (float) Math.sin(hrAng) * outerR * 0.45f,
                            paint);

                    paint.setStrokeWidth(4.8f);
                    canvas.drawLine(
                            -(float) Math.cos(minAng) * s * 0.1f, -(float) Math.sin(minAng) * s * 0.1f,
                            (float) Math.cos(minAng) * outerR * 0.65f, (float) Math.sin(minAng) * outerR * 0.65f,
                            paint);

                    paint.setColor(Color.argb(Math.round(alpha * 0.94f), 255, 175, 92));
                    paint.setStrokeWidth(2.4f);
                    canvas.drawLine(
                            -(float) Math.cos(secAng) * s * 0.12f, -(float) Math.sin(secAng) * s * 0.12f,
                            (float) Math.cos(secAng) * outerR * 0.72f, (float) Math.sin(secAng) * outerR * 0.72f,
                            paint);

                    paint.setStyle(Paint.Style.FILL);
                    paint.setColor(Color.argb(alpha, 255, 240, 215));
                    canvas.drawCircle(0f, 0f, 6.5f, paint);
                } else {
                    canvas.drawCircle(0f, 0f, s * 0.82f, paint);
                    canvas.drawLine(0f, 0f, 0f, -s * 0.48f, paint);
                    canvas.drawLine(0f, 0f, s * 0.42f, 0f, paint);
                }
                break;
            }
            case "home": {
                path.reset();
                path.moveTo(0f, -s * 0.72f);
                path.lineTo(-s * 0.78f, -s * 0.04f);
                path.lineTo(-s * 0.52f, -s * 0.04f);
                path.lineTo(-s * 0.52f, s * 0.68f);
                path.lineTo(-s * 0.16f, s * 0.68f);
                path.lineTo(-s * 0.16f, s * 0.16f);
                path.lineTo(s * 0.16f, s * 0.16f);
                path.lineTo(s * 0.16f, s * 0.68f);
                path.lineTo(s * 0.52f, s * 0.68f);
                path.lineTo(s * 0.52f, -s * 0.04f);
                path.lineTo(s * 0.78f, -s * 0.04f);
                path.close();
                canvas.drawPath(path, paint);
                break;
            }
            case "search": {
                canvas.drawCircle(-s * 0.1f, -s * 0.1f, s * 0.52f, paint);
                canvas.drawLine(s * 0.28f, s * 0.28f, s * 0.72f, s * 0.72f, paint);
                break;
            }
            case "mic": {
                rectF.set(-s * 0.26f, -s * 0.75f, s * 0.26f, s * 0.17f);
                canvas.drawRoundRect(rectF, s * 0.26f, s * 0.26f, paint);
                rectF.set(-s * 0.5f, -s * 0.68f, s * 0.5f, s * 0.32f);
                canvas.drawArc(rectF, 0f, 180f, false, paint);
                canvas.drawLine(0f, s * 0.32f, 0f, s * 0.72f, paint);
                canvas.drawLine(-s * 0.32f, s * 0.72f, s * 0.32f, s * 0.72f, paint);
                break;
            }
            case "apps": {
                float g = s * 0.36f;
                float r = s * 0.24f;
                float[][] pts = new float[][]{{-g, -g}, {g, -g}, {-g, g}, {g, g}};
                for (float[] pt : pts) {
                    rectF.set(pt[0] - r, pt[1] - r, pt[0] + r, pt[1] + r);
                    canvas.drawRoundRect(rectF, s * 0.08f, s * 0.08f, paint);
                }
                break;
            }
            case "tv": {
                rectF.set(-s * 0.78f, -s * 0.38f, s * 0.78f, s * 0.7f);
                canvas.drawRoundRect(rectF, s * 0.14f, s * 0.14f, paint);
                rectF.set(-s * 0.6f, -s * 0.22f, s * 0.36f, s * 0.54f);
                canvas.drawRoundRect(rectF, s * 0.06f, s * 0.06f, paint);
                canvas.drawLine(-s * 0.35f, -s * 0.76f, 0f, -s * 0.38f, paint);
                canvas.drawLine(0f, -s * 0.38f, s * 0.38f, -s * 0.76f, paint);
                break;
            }
            case "channels": {
                canvas.drawCircle(0f, -s * 0.2f, s * 0.14f, paint);
                rectF.set(-s * 0.42f, -s * 0.62f, s * 0.42f, s * 0.22f);
                canvas.drawArc(rectF, -135f, 90f, false, paint);
                canvas.drawArc(rectF, 45f, 90f, false, paint);
                canvas.drawLine(-s * 0.32f, s * 0.72f, 0f, -s * 0.06f, paint);
                canvas.drawLine(0f, -s * 0.06f, s * 0.32f, s * 0.72f, paint);
                break;
            }
            case "hdmi_generic":
            case "hdmi1":
            case "hdmi2":
            case "hdmi3":
            case "hdmi4":
            case "earc": {
                float topY = isHero ? -s * 0.48f : -s * 0.38f;
                float midY = isHero ? s * 0.02f : s * 0.04f;
                float botY = isHero ? s * 0.28f : s * 0.26f;
                float wTop = s * 0.86f;
                float wBot = s * 0.62f;

                path.reset();
                path.moveTo(-wTop, topY);
                path.lineTo(wTop, topY);
                path.lineTo(wTop, midY);
                path.lineTo(wBot, botY);
                path.lineTo(-wBot, botY);
                path.lineTo(-wTop, midY);
                path.close();
                canvas.drawPath(path, paint);
                canvas.drawLine(-s * 0.5f, (topY + botY) * 0.45f, s * 0.5f, (topY + botY) * 0.45f, paint);

                if (!"hdmi_generic".equals(type)) {
                    String badge = "earc".equals(type) ? "eARC" : type.replace("hdmi", "HDMI ");
                    textPaint.reset();
                    textPaint.setAntiAlias(true);
                    textPaint.setTypeface(sansTypeface);
                    textPaint.setFakeBoldText(true);
                    textPaint.setTextSize(isHero ? s * 0.28f : s * 0.34f);
                    textPaint.setTextAlign(Paint.Align.CENTER);
                    textPaint.setColor(col);
                    canvas.drawText(badge, 0f, botY + s * 0.42f, textPaint);
                }
                break;
            }
            case "usb": {
                canvas.drawCircle(0f, s * 0.62f, s * 0.14f, paint);
                canvas.drawLine(0f, s * 0.48f, 0f, -s * 0.68f, paint);
                canvas.drawLine(-s * 0.16f, -s * 0.48f, 0f, -s * 0.72f, paint);
                canvas.drawLine(0f, -s * 0.72f, s * 0.16f, -s * 0.48f, paint);
                canvas.drawLine(0f, s * 0.18f, -s * 0.42f, -s * 0.08f, paint);
                canvas.drawLine(-s * 0.42f, -s * 0.08f, -s * 0.42f, -s * 0.32f, paint);
                canvas.drawCircle(-s * 0.42f, -s * 0.42f, s * 0.1f, paint);
                canvas.drawLine(0f, 0f, s * 0.42f, -s * 0.24f, paint);
                canvas.drawLine(s * 0.42f, -s * 0.24f, s * 0.42f, -s * 0.42f, paint);
                canvas.drawRect(s * 0.32f, -s * 0.62f, s * 0.52f, -s * 0.42f, paint);
                break;
            }
            case "bluetooth": {
                path.reset();
                path.moveTo(-s * 0.38f, -s * 0.38f);
                path.lineTo(s * 0.36f, s * 0.38f);
                path.lineTo(0f, s * 0.76f);
                path.lineTo(0f, -s * 0.76f);
                path.lineTo(s * 0.36f, -s * 0.38f);
                path.lineTo(-s * 0.38f, s * 0.38f);
                canvas.drawPath(path, paint);
                break;
            }
            case "wifi": {
                float[] rs = new float[]{0.28f, 0.54f, 0.8f};
                for (float r : rs) {
                    float rad = s * r;
                    rectF.set(-rad, s * 0.35f - rad, rad, s * 0.35f + rad);
                    canvas.drawArc(rectF, -140f, 100f, false, paint);
                }
                paint.setStyle(Paint.Style.FILL);
                canvas.drawCircle(0f, s * 0.42f, s * 0.08f, paint);
                break;
            }
            case "picture": {
                canvas.drawCircle(0f, 0f, s * 0.36f, paint);
                for (int i = 0; i < 8; i++) {
                    double a = (i * Math.PI) / 4.0;
                    canvas.drawLine(
                            (float) Math.cos(a) * s * 0.52f, (float) Math.sin(a) * s * 0.52f,
                            (float) Math.cos(a) * s * 0.74f, (float) Math.sin(a) * s * 0.74f,
                            paint);
                }
                break;
            }
            case "sound": {
                path.reset();
                path.moveTo(-s * 0.65f, -s * 0.24f);
                path.lineTo(-s * 0.32f, -s * 0.24f);
                path.lineTo(s * 0.05f, -s * 0.62f);
                path.lineTo(s * 0.05f, s * 0.62f);
                path.lineTo(-s * 0.32f, s * 0.24f);
                path.lineTo(-s * 0.65f, s * 0.24f);
                path.close();
                canvas.drawPath(path, paint);
                float[] rs = new float[]{0.32f, 0.58f};
                for (float r : rs) {
                    float rad = s * r;
                    rectF.set(s * 0.1f - rad, -rad, s * 0.1f + rad, rad);
                    canvas.drawArc(rectF, -60f, 120f, false, paint);
                }
                break;
            }
            case "settings": {
                int teeth = 8;
                float outer = s * 0.76f;
                float inner = s * 0.55f;
                path.reset();
                for (int i = 0; i < teeth * 2; i++) {
                    float r = (i % 2 == 0) ? outer : inner;
                    double a = (i * Math.PI) / teeth;
                    float px = (float) Math.cos(a) * r;
                    float py = (float) Math.sin(a) * r;
                    if (i == 0) path.moveTo(px, py);
                    else path.lineTo(px, py);
                }
                path.close();
                canvas.drawPath(path, paint);
                canvas.drawCircle(0f, 0f, s * 0.25f, paint);
                break;
            }
            case "netflix": {
                float w = s * 0.56f;
                float h = s * 0.88f;
                float bar = s * 0.22f;
                canvas.drawRect(-w, -h, -w + bar, h, paint);
                canvas.drawRect(w - bar, -h, w, h, paint);
                path.reset();
                path.moveTo(-w, -h);
                path.lineTo(-w + bar, -h);
                path.lineTo(w, h);
                path.lineTo(w - bar, h);
                path.close();
                paint.setStyle(Paint.Style.FILL);
                paint.setColor(Color.argb(Math.round(alpha * 0.75f), 14, 20, 28));
                canvas.drawPath(path, paint);
                paint.setStyle(Paint.Style.STROKE);
                paint.setColor(col);
                canvas.drawPath(path, paint);
                break;
            }
            case "youtube": {
                rectF.set(-s * 0.82f, -s * 0.56f, s * 0.82f, s * 0.56f);
                canvas.drawRoundRect(rectF, s * 0.26f, s * 0.26f, paint);
                path.reset();
                path.moveTo(-s * 0.2f, -s * 0.26f);
                path.lineTo(s * 0.32f, 0f);
                path.lineTo(-s * 0.2f, s * 0.26f);
                path.close();
                canvas.drawPath(path, paint);
                break;
            }
            case "prime": {
                if (isHero) {
                    textPaint.reset();
                    textPaint.setAntiAlias(true);
                    textPaint.setTypeface(brushTypeface);
                    textPaint.setTextSize(s * 0.42f);
                    textPaint.setTextAlign(Paint.Align.CENTER);
                    textPaint.setColor(col);
                    canvas.drawText("PRIME", 0f, -s * 0.05f, textPaint);
                }
                rectF.set(-s * 0.82f, -s * 1.14f, s * 0.82f, s * 0.5f);
                canvas.drawArc(rectF, 60f, 60f, false, paint);
                canvas.drawLine(s * 0.24f, s * 0.34f, s * 0.44f, s * 0.38f, paint);
                canvas.drawLine(s * 0.44f, s * 0.38f, s * 0.36f, s * 0.55f, paint);
                break;
            }
            case "disney": {
                rectF.set(-s * 0.72f, -s * 0.58f, s * 0.72f, s * 0.86f);
                canvas.drawArc(rectF, 200f, 140f, false, paint);
                textPaint.reset();
                textPaint.setAntiAlias(true);
                textPaint.setTypeface(serifItalicTypeface);
                textPaint.setTextSize(s * 0.44f);
                textPaint.setTextAlign(Paint.Align.CENTER);
                textPaint.setColor(col);
                canvas.drawText("Disney+", 0f, s * 0.28f, textPaint);
                break;
            }
            case "appletv": {
                // Iconic Monochrome White Stroke Apple Logo + "tv" matching Netflix/Prime/Disney+/YouTube!
                float ox = isHero ? -s * 0.32f : -s * 0.28f;
                float oy = s * 0.05f;
                float a = isHero ? s * 0.42f : s * 0.38f;

                path.reset();
                // Bottom center cleft of apple
                path.moveTo(ox, oy + a * 0.78f);
                // Left lobe
                path.cubicTo(ox - a * 0.45f, oy + a * 0.95f, ox - a * 0.98f, oy + a * 0.35f, ox - a * 0.92f, oy - a * 0.22f);
                // Top-left shoulder
                path.cubicTo(ox - a * 0.86f, oy - a * 0.75f, ox - a * 0.38f, oy - a * 0.85f, ox, oy - a * 0.65f);
                // Top-right shoulder
                path.cubicTo(ox + a * 0.36f, oy - a * 0.85f, ox + a * 0.78f, oy - a * 0.72f, ox + a * 0.86f, oy - a * 0.38f);
                // Right side bite indentation
                path.cubicTo(ox + a * 0.52f, oy - a * 0.20f, ox + a * 0.52f, oy + a * 0.25f, ox + a * 0.88f, oy + a * 0.40f);
                // Right bottom lobe back to cleft
                path.cubicTo(ox + a * 0.72f, oy + a * 0.85f, ox + a * 0.38f, oy + a * 0.95f, ox, oy + a * 0.78f);
                path.close();
                canvas.drawPath(path, paint);

                // Apple top leaf
                path.reset();
                path.moveTo(ox + a * 0.02f, oy - a * 0.72f);
                path.quadTo(ox + a * 0.05f, oy - a * 1.18f, ox + a * 0.42f, oy - a * 1.22f);
                path.quadTo(ox + a * 0.40f, oy - a * 0.78f, ox + a * 0.02f, oy - a * 0.72f);
                canvas.drawPath(path, paint);

                // Clean "tv" typography beside the Apple mark
                textPaint.reset();
                textPaint.setAntiAlias(true);
                textPaint.setTypeface(sansTypeface);
                textPaint.setFakeBoldText(true);
                textPaint.setTextSize(isHero ? s * 0.62f : s * 0.56f);
                textPaint.setTextAlign(Paint.Align.LEFT);
                textPaint.setColor(col);
                canvas.drawText("tv", ox + a * 1.05f, oy + a * 0.52f, textPaint);
                break;
            }
            case "crunchyroll": {
                // Iconic Monochrome White Stroke Crunchyroll Eye / Swirl Crest!
                // 1. Outer sweeping C-arc
                rectF.set(-s * 0.78f, -s * 0.78f, s * 0.78f, s * 0.78f);
                canvas.drawArc(rectF, 35f, 300f, false, paint);

                // 2. Inner offset eye circle shifted slightly down-right
                float ix = s * 0.12f;
                float iy = s * 0.10f;
                float ir = s * 0.48f;
                canvas.drawCircle(ix, iy, ir, paint);

                // 3. Eye pupil cutout arc / dot on top-left of inner circle
                paint.setStyle(Paint.Style.FILL);
                canvas.drawCircle(ix - ir * 0.36f, iy - ir * 0.32f, s * 0.13f, paint);
                paint.setStyle(Paint.Style.STROKE);
                break;
            }
            case "bbc_iplayer": {
                // Iconic 3 BBC Blocks + Play / iPlayer vector crest
                float bw = s * 0.44f;
                float bh = s * 0.36f;
                float gap = s * 0.08f;
                float topY = isHero ? -s * 0.58f : -s * 0.46f;
                String[] letters = new String[]{"B", "B", "C"};

                textPaint.reset();
                textPaint.setAntiAlias(true);
                textPaint.setTypeface(sansTypeface);
                textPaint.setFakeBoldText(true);
                textPaint.setTextSize(bh * 0.78f);
                textPaint.setTextAlign(Paint.Align.CENTER);
                textPaint.setColor(col);

                for (int i = 0; i < 3; i++) {
                    float bx = (i - 1) * (bw + gap);
                    rectF.set(bx - bw * 0.5f, topY, bx + bw * 0.5f, topY + bh);
                    canvas.drawRoundRect(rectF, s * 0.05f, s * 0.05f, paint);
                    canvas.drawText(letters[i], bx, topY + bh * 0.78f, textPaint);
                }

                // Play triangle below BBC blocks
                path.reset();
                float py = topY + bh + s * 0.44f;
                path.moveTo(-s * 0.24f, py - s * 0.24f);
                path.lineTo(s * 0.28f, py);
                path.lineTo(-s * 0.24f, py + s * 0.24f);
                path.close();
                canvas.drawPath(path, paint);
                break;
            }
            case "bbc_sounds": {
                // Iconic 3 BBC Blocks + Soundwave curves
                float bw = s * 0.44f;
                float bh = s * 0.36f;
                float gap = s * 0.08f;
                float topY = isHero ? -s * 0.58f : -s * 0.46f;
                String[] letters = new String[]{"B", "B", "C"};

                textPaint.reset();
                textPaint.setAntiAlias(true);
                textPaint.setTypeface(sansTypeface);
                textPaint.setFakeBoldText(true);
                textPaint.setTextSize(bh * 0.78f);
                textPaint.setTextAlign(Paint.Align.CENTER);
                textPaint.setColor(col);

                for (int i = 0; i < 3; i++) {
                    float bx = (i - 1) * (bw + gap);
                    rectF.set(bx - bw * 0.5f, topY, bx + bw * 0.5f, topY + bh);
                    canvas.drawRoundRect(rectF, s * 0.05f, s * 0.05f, paint);
                    canvas.drawText(letters[i], bx, topY + bh * 0.78f, textPaint);
                }

                // Equalizer / sound bars underneath
                float baseBarY = topY + bh + s * 0.42f;
                float[] heights = new float[]{0.14f, 0.26f, 0.34f, 0.22f, 0.30f, 0.14f};
                for (int i = 0; i < heights.length; i++) {
                    float lx = (i - 2.5f) * s * 0.22f;
                    float hh = heights[i] * s;
                    canvas.drawLine(lx, baseBarY - hh, lx, baseBarY + hh, paint);
                }
                break;
            }
            case "rte_player": {
                // Iconic RTÉ Geometric Frame + Play Triangle
                rectF.set(-s * 0.84f, -s * 0.52f, s * 0.84f, s * 0.52f);
                canvas.drawRoundRect(rectF, s * 0.16f, s * 0.16f, paint);

                textPaint.reset();
                textPaint.setAntiAlias(true);
                textPaint.setTypeface(sansTypeface);
                textPaint.setFakeBoldText(true);
                textPaint.setTextSize(s * 0.46f);
                textPaint.setTextAlign(Paint.Align.CENTER);
                textPaint.setColor(col);
                canvas.drawText("RTÉ", 0f, s * 0.16f, textPaint);
                // Fada accent above É
                canvas.drawLine(s * 0.32f, -s * 0.24f, s * 0.46f, -s * 0.34f, paint);
                break;
            }
            case "browser": {
                // Clean Globe + Meridian Arcs
                float r = s * 0.74f;
                canvas.drawCircle(0f, 0f, r, paint);
                rectF.set(-r * 0.48f, -r, r * 0.48f, r);
                canvas.drawOval(rectF, paint);
                canvas.drawLine(-r, 0f, r, 0f, paint);
                canvas.drawLine(-r * 0.86f, -r * 0.45f, r * 0.86f, -r * 0.45f, paint);
                canvas.drawLine(-r * 0.86f, r * 0.45f, r * 0.86f, r * 0.45f, paint);
                break;
            }
            case "playstore": {
                path.reset();
                path.moveTo(-s * 0.52f, -s * 0.7f);
                path.lineTo(s * 0.65f, 0f);
                path.lineTo(-s * 0.52f, s * 0.7f);
                path.close();
                canvas.drawPath(path, paint);
                canvas.drawLine(-s * 0.52f, -s * 0.7f, s * 0.14f, 0f, paint);
                canvas.drawLine(s * 0.14f, 0f, -s * 0.52f, s * 0.7f, paint);
                break;
            }
            case "gamepad": {
                rectF.set(-s * 0.78f, -s * 0.42f, s * 0.78f, s * 0.42f);
                canvas.drawRoundRect(rectF, s * 0.36f, s * 0.36f, paint);
                canvas.drawLine(-s * 0.48f, 0f, -s * 0.24f, 0f, paint);
                canvas.drawLine(-s * 0.36f, -s * 0.12f, -s * 0.36f, s * 0.12f, paint);
                paint.setStyle(Paint.Style.FILL);
                canvas.drawCircle(s * 0.32f, -s * 0.08f, s * 0.06f, paint);
                canvas.drawCircle(s * 0.46f, s * 0.08f, s * 0.06f, paint);
                break;
            }
            case "cast": {
                rectF.set(-s * 0.75f, -s * 0.55f, s * 0.75f, s * 0.55f);
                canvas.drawRoundRect(rectF, s * 0.12f, s * 0.12f, paint);
                float[] rs = new float[]{0.24f, 0.46f};
                for (float r : rs) {
                    float rad = s * r;
                    rectF.set(-s * 0.75f - rad, s * 0.55f - rad, -s * 0.75f + rad, s * 0.55f + rad);
                    canvas.drawArc(rectF, -90f, 90f, false, paint);
                }
                break;
            }
            case "shield": {
                // Proton VPN Shield + Inner Orbital Triangle
                path.reset();
                path.moveTo(0f, -s * 0.78f);
                path.lineTo(s * 0.64f, -s * 0.46f);
                path.lineTo(s * 0.50f, s * 0.28f);
                path.lineTo(0f, s * 0.78f);
                path.lineTo(-s * 0.50f, s * 0.28f);
                path.lineTo(-s * 0.64f, -s * 0.46f);
                path.close();
                canvas.drawPath(path, paint);

                // Inner Proton triangle nodes
                path.reset();
                path.moveTo(-s * 0.28f, -s * 0.22f);
                path.lineTo(s * 0.30f, -s * 0.12f);
                path.lineTo(-s * 0.04f, s * 0.34f);
                path.close();
                canvas.drawPath(path, paint);
                break;
            }
            case "moon": {
                canvas.drawCircle(0f, 0f, s * 0.62f, paint);
                break;
            }
            case "app_custom":
            default: {
                // Always stay 100% in the white monochrome stroke theme!
                rectF.set(-s * 0.72f, -s * 0.54f, s * 0.72f, s * 0.54f);
                canvas.drawRoundRect(rectF, s * 0.18f, s * 0.18f, paint);
                path.reset();
                path.moveTo(-s * 0.18f, -s * 0.24f);
                path.lineTo(s * 0.28f, 0f);
                path.lineTo(-s * 0.18f, s * 0.24f);
                path.close();
                canvas.drawPath(path, paint);
                break;
            }
        }

        if (!isHero && smallCaption != null && !smallCaption.isEmpty()
                && !type.startsWith("hdmi") && !"earc".equals(type) && !"disney".equals(type)) {
            textPaint.reset();
            textPaint.setAntiAlias(true);
            textPaint.setTypeface(sansTypeface);
            textPaint.setTextSize(12.5f);
            textPaint.setTextAlign(Paint.Align.CENTER);
            textPaint.setColor(Color.argb(Math.round(alpha * 0.80f), 205, 222, 240));
            canvas.drawText(smallCaption, 0f, s * 1.04f, textPaint);
        }

        canvas.restore();
    }
}
