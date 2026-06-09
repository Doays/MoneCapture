const MONE_OPTIONS_KEY = "moneOptions";
const MONE_SCREENSHOT_DELAY_DEFAULT_SECONDS = 1;
const MONE_SCREENSHOT_DELAY_MIN_SECONDS = 0.01;
const MONE_SCREENSHOT_DELAY_MAX_SECONDS = 5;
const MONE_CONTINUOUS_CAPTURE_DEFAULT_INTERVAL_MS = 17;
const MONE_CONTINUOUS_CAPTURE_MIN_INTERVAL_MS = 17;
const MONE_CONTINUOUS_CAPTURE_MAX_INTERVAL_MS = 1000;
const MONE_CONTINUOUS_CAPTURE_START_DELAY_DEFAULT_MS = 450;
const MONE_CONTINUOUS_CAPTURE_START_DELAY_MIN_MS = 150;
const MONE_CONTINUOUS_CAPTURE_START_DELAY_MAX_MS = 1500;
const MONE_DELAYED_FRAME_CACHE_DEFAULT_SECONDS = 5;
const MONE_DELAYED_FRAME_CACHE_MIN_SECONDS = 0.5;
const MONE_DELAYED_FRAME_CACHE_MAX_SECONDS = 5;

const MONE_DELAYED_FRAME_CACHE_PRESETS = {
  performance: {
    intervalMs: 200,
    maxWidth: 960,
    maxFrames: 30,
  },
  balanced: {
    intervalMs: 50,
    maxWidth: 1280,
    maxFrames: 100,
  },
  highspeed: {
    intervalMs: 17,
    maxWidth: 1280,
    maxFrames: 240,
  },
  original: {
    intervalMs: 50,
    maxWidth: 0,
    maxFrames: 80,
  },
};

const MONE_DEFAULT_OPTIONS = {
  screenshot: true,
  record: true,
  pip: false,
  seek: true,
  lowLatency: true,
  toolbarVisible: true,
  screenshotDelay: true,
  screenshotDelaySeconds: MONE_SCREENSHOT_DELAY_DEFAULT_SECONDS,
  continuousCapture: true,
  continuousCaptureIntervalMs: MONE_CONTINUOUS_CAPTURE_DEFAULT_INTERVAL_MS,
  continuousInstantCaptureIntervalMs: MONE_CONTINUOUS_CAPTURE_DEFAULT_INTERVAL_MS,
  continuousDelayedCaptureIntervalMs: MONE_CONTINUOUS_CAPTURE_DEFAULT_INTERVAL_MS,
  continuousCaptureStartDelayMs: MONE_CONTINUOUS_CAPTURE_START_DELAY_DEFAULT_MS,
  delayedFrameCacheSeconds: MONE_DELAYED_FRAME_CACHE_DEFAULT_SECONDS,
  delayedFrameCachePreset: "original",
  toolbarPlacement: "info",
  saveMode: "folder",
  recordingPreset: "performance",
  bitrate: 4000000,
  screenshotKey: "KeyS",
  delayedScreenshotKey: "KeyB",
  recordKey: "KeyR",
  seekLeftKey: "ArrowLeft",
  seekRightKey: "ArrowRight",
};

const MONE_RECORDING_PRESETS = {
  performance: {
    defaultBitrate: 4000000,
    maxBitrate: 4000000,
    chunkMs: 3000,
    mimeTypes: [
      "video/mp4;codecs=avc1.42E01E,mp4a.40.2",
      "video/mp4",
      "video/webm;codecs=vp8,opus",
      "video/webm;codecs=vp8",
      "video/webm",
    ],
  },
  balanced: {
    defaultBitrate: 6000000,
    maxBitrate: 6000000,
    chunkMs: 2000,
    mimeTypes: [
      "video/webm;codecs=vp8,opus",
      "video/webm;codecs=vp8",
      "video/mp4;codecs=avc1.42E01E,mp4a.40.2",
      "video/mp4",
      "video/webm",
    ],
  },
  quality: {
    defaultBitrate: 8000000,
    maxBitrate: 8000000,
    chunkMs: 1000,
    mimeTypes: [
      "video/webm;codecs=vp9,opus",
      "video/webm;codecs=vp8,opus",
      "video/mp4;codecs=avc1.42E01E,mp4a.40.2",
      "video/mp4",
      "video/webm",
    ],
  },
};

const MONE_NUMPAD_LABELS = {
  NumpadAdd: "num+",
  NumpadSubtract: "num-",
  NumpadMultiply: "num*",
  NumpadDivide: "num/",
  NumpadDecimal: "num.",
  NumpadEnter: "numEnter",
};

const MONE_KEY_LABELS = {
  ArrowLeft: "ArrowLeft",
  ArrowRight: "ArrowRight",
  ArrowUp: "ArrowUp",
  ArrowDown: "ArrowDown",
  Space: "Space",
  Enter: "Enter",
  Escape: "Esc",
  Tab: "Tab",
  Backspace: "Backspace",
  Delete: "Delete",
  Home: "Home",
  End: "End",
  PageUp: "PageUp",
  PageDown: "PageDown",
};

function moneStorageGet(keys) {
  return new Promise((resolve, reject) => {
    try {
      if (!globalThis.chrome?.storage?.local) {
        reject(new Error("Extension context invalidated."));
        return;
      }
      chrome.storage.local.get(keys, (data) => {
        const error = chrome.runtime?.lastError;
        if (error) {
          reject(new Error(error.message));
          return;
        }
        resolve(data || {});
      });
    } catch (error) {
      reject(error);
    }
  });
}

function moneStorageSet(payload) {
  return new Promise((resolve, reject) => {
    try {
      if (!globalThis.chrome?.storage?.local) {
        reject(new Error("Extension context invalidated."));
        return;
      }
      chrome.storage.local.set(payload, () => {
        const error = chrome.runtime?.lastError;
        if (error) {
          reject(new Error(error.message));
          return;
        }
        resolve();
      });
    } catch (error) {
      reject(error);
    }
  });
}

function moneIsExtensionContextInvalidated(error) {
  return /Extension context invalidated|context invalidated/i.test(String(error?.message || error || ""));
}

function moneNormalizeOptions(options) {
  const normalized = { ...MONE_DEFAULT_OPTIONS, ...(options || {}) };
  if (normalized.toolbarPlacement === "video") {
    normalized.toolbarPlacement = "info";
  }
  if (!MONE_RECORDING_PRESETS[normalized.recordingPreset]) {
    normalized.recordingPreset = MONE_DEFAULT_OPTIONS.recordingPreset;
  }
  normalized.pip = false;
  normalized.bitrate = moneDefaultBitrateForPreset(normalized.recordingPreset);
  normalized.screenshotDelay = true;
  normalized.screenshotDelaySeconds = moneNormalizeScreenshotDelaySeconds(normalized.screenshotDelaySeconds);
  normalized.continuousCapture = Boolean(normalized.continuousCapture);
  const legacyContinuousInterval = normalized.continuousCaptureIntervalMs;
  normalized.continuousInstantCaptureIntervalMs = moneNormalizeContinuousCaptureIntervalMs(normalized.continuousInstantCaptureIntervalMs ?? legacyContinuousInterval);
  normalized.continuousDelayedCaptureIntervalMs = moneNormalizeContinuousCaptureIntervalMs(normalized.continuousDelayedCaptureIntervalMs ?? legacyContinuousInterval);
  normalized.continuousCaptureIntervalMs = normalized.continuousInstantCaptureIntervalMs;
  normalized.continuousCaptureStartDelayMs = moneNormalizeContinuousCaptureStartDelayMs(normalized.continuousCaptureStartDelayMs);
  normalized.delayedFrameCacheSeconds = moneNormalizeDelayedFrameCacheSeconds(normalized.delayedFrameCacheSeconds);
  if (!MONE_DELAYED_FRAME_CACHE_PRESETS[normalized.delayedFrameCachePreset]) {
    normalized.delayedFrameCachePreset = MONE_DEFAULT_OPTIONS.delayedFrameCachePreset;
  }
  return normalized;
}

function moneNormalizeScreenshotDelaySeconds(value) {
  const parsed = Number(value);
  if (!Number.isFinite(parsed)) {
    return MONE_SCREENSHOT_DELAY_DEFAULT_SECONDS;
  }
  const clamped = Math.min(MONE_SCREENSHOT_DELAY_MAX_SECONDS, Math.max(MONE_SCREENSHOT_DELAY_MIN_SECONDS, parsed));
  return Math.round(clamped * 100) / 100;
}

function moneNormalizeContinuousCaptureIntervalMs(value) {
  const parsed = Number(value);
  if (!Number.isFinite(parsed)) {
    return MONE_CONTINUOUS_CAPTURE_DEFAULT_INTERVAL_MS;
  }
  return Math.round(Math.min(MONE_CONTINUOUS_CAPTURE_MAX_INTERVAL_MS, Math.max(MONE_CONTINUOUS_CAPTURE_MIN_INTERVAL_MS, parsed)));
}

function moneNormalizeContinuousCaptureStartDelayMs(value) {
  const parsed = Number(value);
  if (!Number.isFinite(parsed)) {
    return MONE_CONTINUOUS_CAPTURE_START_DELAY_DEFAULT_MS;
  }
  return Math.round(Math.min(MONE_CONTINUOUS_CAPTURE_START_DELAY_MAX_MS, Math.max(MONE_CONTINUOUS_CAPTURE_START_DELAY_MIN_MS, parsed)));
}

function moneNormalizeDelayedFrameCacheSeconds(value) {
  const parsed = Number(value);
  if (!Number.isFinite(parsed)) {
    return MONE_DELAYED_FRAME_CACHE_DEFAULT_SECONDS;
  }
  const clamped = Math.min(MONE_DELAYED_FRAME_CACHE_MAX_SECONDS, Math.max(MONE_DELAYED_FRAME_CACHE_MIN_SECONDS, parsed));
  return Math.round(clamped * 10) / 10;
}

function moneDelayedFrameCachePreset(name) {
  return MONE_DELAYED_FRAME_CACHE_PRESETS[name] || MONE_DELAYED_FRAME_CACHE_PRESETS[MONE_DEFAULT_OPTIONS.delayedFrameCachePreset];
}

function moneDefaultBitrateForPreset(presetName) {
  const preset = MONE_RECORDING_PRESETS[presetName] || MONE_RECORDING_PRESETS[MONE_DEFAULT_OPTIONS.recordingPreset];
  return preset.defaultBitrate;
}

function moneEffectiveRecordOptions(options) {
  const normalized = moneNormalizeOptions(options);
  const preset = MONE_RECORDING_PRESETS[normalized.recordingPreset] || MONE_RECORDING_PRESETS.performance;
  return {
    bitrate: Math.min(normalized.bitrate, preset.maxBitrate),
    chunkMs: preset.chunkMs,
    mimeTypes: preset.mimeTypes,
    preset: normalized.recordingPreset,
  };
}

function moneRecordingExtension(mimeType) {
  return /mp4/i.test(String(mimeType || "")) ? "mp4" : "webm";
}

async function moneLoadOptions() {
  const data = await moneStorageGet([MONE_OPTIONS_KEY]);
  return moneNormalizeOptions(data[MONE_OPTIONS_KEY]);
}

async function moneSaveOptions(options) {
  await moneStorageSet({ [MONE_OPTIONS_KEY]: moneNormalizeOptions(options) });
}

function moneEventCode(event) {
  return event?.code && event.code !== "Unidentified" ? event.code : "";
}

function moneLegacyShortcutFromKey(key) {
  if (key === " ") {
    return "Space";
  }
  if (key && key.length === 1) {
    return key.toUpperCase();
  }
  return key || "";
}

function moneShortcutFromEvent(event) {
  if (event.key === "Escape") {
    return "";
  }
  if (["Shift", "Control", "Alt", "Meta"].includes(event.key)) {
    return null;
  }
  return moneEventCode(event) || moneLegacyShortcutFromKey(event.key);
}

function moneShortcutLabel(value) {
  const shortcut = String(value || "");
  if (!shortcut) {
    return "미설정";
  }
  if (/^Key[A-Z]$/.test(shortcut)) {
    return shortcut.slice(3);
  }
  if (/^Digit[0-9]$/.test(shortcut)) {
    return shortcut.slice(5);
  }
  if (/^Numpad[0-9]$/.test(shortcut)) {
    return `num${shortcut.slice(6)}`;
  }
  return MONE_NUMPAD_LABELS[shortcut] || MONE_KEY_LABELS[shortcut] || shortcut;
}

function moneShortcutMatches(event, shortcut) {
  const saved = String(shortcut || "");
  if (!saved) {
    return false;
  }
  if (moneEventCode(event) === saved) {
    return true;
  }
  return moneLegacyShortcutFromKey(event.key).toUpperCase() === saved.toUpperCase();
}
