(() => {
  const ROOT_ID = "mone-capture-video-tools";
  const HOST_ID = "mone-capture-video-toolbar-host";
  const STATUS_ID = "mone-capture-video-status";
  const OVERLAY_ID = "mone-capture-record-overlay";
  const DIRECTORY_DB_NAME = "moneCaptureVideo";
  const DIRECTORY_STORE_NAME = "handles";
  const DIRECTORY_HANDLE_KEY = "saveDirectory";
  const VIDEO_CACHE_MS = 650;
  const SCREENSHOT_CANVAS_POOL_LIMIT = 8;
  const DELAYED_FRAME_CACHE_MAX_BYTES = 384 * 1024 * 1024;
  const DELAYED_FRAME_CACHE_ERROR_BACKOFF_MS = 5000;
  const RECORD_MAX_BUFFER_BYTES = 768 * 1024 * 1024;
  const INJECTION_DELAY_MS = 350;
  const LOW_LATENCY_TARGET_SECONDS = 1.5;
  const LOW_LATENCY_SPEEDUP_SECONDS = 3.5;
  const LOW_LATENCY_CHECK_MS = 2000;
  const LOW_LATENCY_NOTICE_COOLDOWN_MS = 10000;
  const SCREENSHOT_DELAY_SEEK_TIMEOUT_MS = 900;
  const DELAYED_FRAME_CACHE_INTERVAL_MS = 200;
  const DELAYED_FRAME_CACHE_ACTIVE_MS = 15000;
  const DELAYED_FRAME_CACHE_MARGIN_SECONDS = 0.75;
  const DELAYED_FRAME_WARM_CHECK_MS = 750;
  const RECORD_MAX_DURATION_MS = 5 * 60 * 1000;
  const UI_HEALTH_CHECK_MS = 2000;
  const LIVE_DETAIL_CACHE_MS = 30000;

  let options = { ...MONE_DEFAULT_OPTIONS };
  let directoryHandle = null;
  let directoryHandleLoaded = false;
  let directoryPermissionGranted = false;
  let sessionDirectoryRootHandle = null;
  let sessionDirectoryHandle = null;
  let sessionDirectoryName = "";
  let sessionDirectoryKey = "";
  let liveSessionInfoCache = null;
  let liveSessionInfoPromise = null;
  let cachedVideo = null;
  let cachedVideoAt = 0;
  let screenshotCanvasPool = [];
  let saveQueue = Promise.resolve();
  let delayedScreenshotQueue = Promise.resolve();
  let delayedFrameCache = [];
  let delayedFrameCacheIndex = 0;
  let delayedFrameCacheTimer = 0;
  let delayedFrameWarmTimer = 0;
  let delayedFrameCacheActiveUntil = 0;
  let delayedFrameCacheDisabledUntil = 0;
  let continuousCaptureAction = "";
  let continuousCaptureKey = "";
  let continuousCaptureTimer = 0;
  let continuousCaptureRunning = false;
  let pressedCaptureKeys = new Set();
  let mixedCaptureHandled = false;
  let pendingScreenshotSaves = 0;
  let lastStampBase = "";
  let lastStampSerial = 0;
  let optionsLoaded = false;
  let recorder = null;
  let recordChunks = [];
  let recordBufferedBytes = 0;
  let recordStartedAt = 0;
  let recordTimer = 0;
  let recordLimitTimer = 0;
  let lowLatencyEnabled = false;
  let lowLatencyTimer = 0;
  let lowLatencyLastNoticeAt = 0;
  let normalPlaybackRate = 1;
  let injectTimer = 0;
  let positionRaf = 0;
  let uiHealthTimer = 0;
  let nonCaptureActionRunning = "";
  let extensionDisposed = false;
  let shortcutAttached = false;
  let mutationObserver = null;
  let lastUrl = location.href;

  function isSupportedPage() {
    return location.origin === "https://chzzk.naver.com" &&
      (location.pathname.startsWith("/live/") || location.pathname.startsWith("/video/"));
  }

  function isLivePage() {
    return location.origin === "https://chzzk.naver.com" && location.pathname.startsWith("/live/");
  }

  function handleUnsupportedPage() {
    window.clearTimeout(injectTimer);
    injectTimer = 0;
    stopUiHealthCheck();
    stopLowLatency(false);
    stopContinuousCapture();
    stopDelayedFrameWarmMonitor();
    clearDelayedFrameCache();
    resetSessionDirectory();
    removeToolbar();
    document.getElementById(STATUS_ID)?.remove();
    return false;
  }

  function resetSessionDirectory() {
    sessionDirectoryRootHandle = null;
    sessionDirectoryHandle = null;
    sessionDirectoryName = "";
    sessionDirectoryKey = "";
    liveSessionInfoCache = null;
    liveSessionInfoPromise = null;
  }

  function handleUrlChange() {
    if (lastUrl === location.href) {
      return;
    }
    lastUrl = location.href;
    resetSessionDirectory();
    if (!isLivePage() && lowLatencyEnabled) {
      stopLowLatency();
    }
    if (isSupportedPage()) {
      ensureShortcutListeners();
      scheduleInjection();
      scheduleDelayedFrameWarmMonitor();
      scheduleUiHealthCheck(0);
      return;
    }
    handleUnsupportedPage();
  }

  function installUrlChangeHooks() {
    ["pushState", "replaceState"].forEach((method) => {
      const original = history[method];
      history[method] = function patchedHistoryMethod(...args) {
        const result = original.apply(this, args);
        window.setTimeout(handleUrlChange, 0);
        return result;
      };
    });
  }

  function isAbortError(error) {
    return error?.name === "AbortError" || /aborted|user aborted/i.test(String(error?.message || error || ""));
  }

  function disposeExtensionContext() {
    if (extensionDisposed) {
      return;
    }
    extensionDisposed = true;
    window.clearTimeout(injectTimer);
    window.clearTimeout(showStatus.timer);
    stopUiHealthCheck();
      stopContinuousCapture();
      stopDelayedFrameWarmMonitor();
    clearDelayedFrameCache();
    window.cancelAnimationFrame(positionRaf);
    mutationObserver?.disconnect();
    if (shortcutAttached) {
      document.removeEventListener("keydown", handleShortcut, true);
      document.removeEventListener("keyup", handleShortcutKeyup, true);
      shortcutAttached = false;
    }
    removeToolbar();
    document.getElementById(STATUS_ID)?.remove();
  }

  function handleAsyncError(error) {
    if (!error || isAbortError(error)) {
      return;
    }
    if (moneIsExtensionContextInvalidated(error)) {
      disposeExtensionContext();
      return;
    }
    console.info("MoneCapture", error);
  }

  async function loadOptions() {
    options = await moneLoadOptions();
    optionsLoaded = true;
    return options;
  }

  async function ensureOptionsLoaded() {
    if (!optionsLoaded) {
      await loadOptions();
    }
    return options;
  }

  function canPickDirectory() {
    return typeof window.showDirectoryPicker === "function";
  }

  function visibleArea(element) {
    const rect = element.getBoundingClientRect();
    if (rect.width < 4 || rect.height < 4) {
      return 0;
    }
    const style = window.getComputedStyle(element);
    if (style.display === "none" || style.visibility === "hidden" || Number(style.opacity) <= 0) {
      return 0;
    }
    const width = Math.max(0, Math.min(rect.right, window.innerWidth) - Math.max(rect.left, 0));
    const height = Math.max(0, Math.min(rect.bottom, window.innerHeight) - Math.max(rect.top, 0));
    return width * height;
  }

  function clamp(value, min, max) {
    return Math.min(Math.max(value, min), max);
  }

  function findVideo() {
    if (cachedVideo && Date.now() - cachedVideoAt < VIDEO_CACHE_MS && visibleArea(cachedVideo) > 0) {
      return cachedVideo;
    }
    const videos = Array.from(document.querySelectorAll("video"));
    cachedVideo = videos
      .map((video) => ({
        video,
        score: (video.classList.contains("webplayer-internal-video") ? 10000000 : 0) + visibleArea(video),
      }))
      .filter((item) => item.score > 0)
      .sort((a, b) => b.score - a.score)[0]?.video || null;
    cachedVideoAt = Date.now();
    return cachedVideo;
  }

  function clearToolbarPosition(root) {
    root.style.left = "";
    root.style.top = "";
    root.style.right = "";
    root.style.bottom = "";
  }

  function findInfoAnchor(video) {
    const title = document.querySelector("h2[class*='video_information_title']");
    const titleRow = title?.closest("[class*='video_information_row']") || title?.parentElement;
    if (titleRow) {
      return titleRow;
    }

    const row = document.querySelector("[class*='video_information_row']");
    if (row) {
      return row;
    }

    return null;
  }

  function attachToolbar(root, video = findVideo()) {
    if (!root) {
      return;
    }

    if (options.toolbarPlacement === "info") {
      const anchor = findInfoAnchor(video);
      if (anchor) {
        let host = document.getElementById(HOST_ID);
        if (!host) {
          host = document.createElement("div");
          host.id = HOST_ID;
          host.className = "mone-capture-toolbar-host";
        }
        anchor.classList.add("mone-capture-toolbar-row");
        if (host.parentElement !== anchor) {
          host.parentElement?.classList.remove("mone-capture-toolbar-row");
          anchor.appendChild(host);
        }
        root.className = "mone-capture-video-tools inline";
        clearToolbarPosition(root);
        host.appendChild(root);
        return;
      }
    }

    root.className = "mone-capture-video-tools floating";
    document.documentElement.appendChild(root);
    const host = document.getElementById(HOST_ID);
    if (host && !host.childElementCount) {
      host.parentElement?.classList.remove("mone-capture-toolbar-row");
      host.remove();
    }
    positionToolbar(root, video);
  }

  function positionToolbar(root, video = findVideo()) {
    if (!root) {
      return;
    }
    if (!root.classList.contains("floating")) {
      clearToolbarPosition(root);
      return;
    }
    if (options.toolbarPlacement === "viewport" || !video) {
      clearToolbarPosition(root);
      return;
    }

    const rect = video.getBoundingClientRect();
    if (rect.width < 4 || rect.height < 4) {
      return;
    }

    const margin = 12;
    const width = root.offsetWidth || 236;
    const height = root.offsetHeight || 48;
    const viewportMaxLeft = Math.max(margin, window.innerWidth - width - margin);
    const viewportMaxTop = Math.max(margin, window.innerHeight - height - margin);
    const videoRight = clamp(rect.right, margin, window.innerWidth);
    const videoBottom = clamp(rect.bottom, margin, window.innerHeight);
    const left = clamp(videoRight - width - margin, margin, viewportMaxLeft);
    const top = clamp(videoBottom - height - margin, margin, viewportMaxTop);

    root.style.left = `${Math.round(left)}px`;
    root.style.top = `${Math.round(top)}px`;
    root.style.right = "auto";
    root.style.bottom = "auto";
  }

  function sanitizeFileName(value) {
    return String(value || "video")
      .replace(/[<>:"/\\|?*\x00-\x1f]/g, "_")
      .replace(/\s+/g, " ")
      .trim()
      .replace(/[. ]+$/g, "") || "video";
  }

  function limitFileName(value, maxLength = 120) {
    const name = sanitizeFileName(value);
    return name.length > maxLength ? name.slice(0, maxLength).replace(/[. ]+$/g, "") : name;
  }

  function dateStamp(date = new Date()) {
    const pad = (value) => String(value).padStart(2, "0");
    return `${date.getFullYear()}${pad(date.getMonth() + 1)}${pad(date.getDate())}`;
  }

  function stamp() {
    const now = new Date();
    const pad = (value, size = 2) => String(value).padStart(size, "0");
    const base = `${now.getFullYear()}${pad(now.getMonth() + 1)}${pad(now.getDate())}-${pad(now.getHours())}${pad(now.getMinutes())}${pad(now.getSeconds())}-${pad(now.getMilliseconds(), 3)}`;
    if (base === lastStampBase) {
      lastStampSerial += 1;
    } else {
      lastStampBase = base;
      lastStampSerial = 0;
    }
    return lastStampSerial ? `${base}-${lastStampSerial}` : base;
  }

  function streamTitle() {
    return document.title.replace(/\s*-\s*CHZZK\s*$/i, "") || location.hostname || "video";
  }

  function sessionFolderName(title = streamTitle()) {
    return `${dateStamp()} ${limitFileName(title, 150)}`;
  }

  function pathSessionDirectoryKey() {
    if (!isSupportedPage()) {
      return "";
    }
    return `${location.origin}${location.pathname.replace(/\/+$/g, "")}`;
  }

  function liveChannelId() {
    const match = location.pathname.match(/^\/live\/([^/?#]+)/);
    return match ? decodeURIComponent(match[1]) : "";
  }

  async function fetchLiveSessionInfo(channelId) {
    try {
      const response = await fetch(`https://api.chzzk.naver.com/service/v3/channels/${encodeURIComponent(channelId)}/live-detail`, {
        cache: "no-store",
        credentials: "include",
      });
      if (!response.ok) {
        throw new Error(`live-detail ${response.status}`);
      }
      const payload = await response.json();
      const content = payload?.content || payload;
      const liveId = content?.liveId ?? content?.livePlayback?.meta?.liveId;
      const openDate = content?.openDate || content?.livePlayback?.live?.open || content?.livePlayback?.live?.start;
      if (!liveId && !openDate) {
        return null;
      }
      return {
        key: `live:${channelId}:${liveId || ""}:${openDate || ""}`,
        title: content?.liveTitle || "",
      };
    } catch (error) {
      console.info("MoneCapture live session lookup skipped", error);
      return null;
    }
  }

  async function liveSessionInfo() {
    const channelId = liveChannelId();
    if (!channelId) {
      return null;
    }
    const now = Date.now();
    if (liveSessionInfoCache?.channelId === channelId && now - liveSessionInfoCache.fetchedAt < LIVE_DETAIL_CACHE_MS) {
      return liveSessionInfoCache.info;
    }
    if (liveSessionInfoPromise?.channelId === channelId) {
      return liveSessionInfoPromise.promise;
    }
    const promise = fetchLiveSessionInfo(channelId).then((info) => {
      liveSessionInfoCache = { channelId, fetchedAt: Date.now(), info };
      return info;
    }).finally(() => {
      if (liveSessionInfoPromise?.promise === promise) {
        liveSessionInfoPromise = null;
      }
    });
    liveSessionInfoPromise = { channelId, promise };
    return promise;
  }

  async function currentSessionDirectoryInfo() {
    const pathKey = pathSessionDirectoryKey();
    if (!pathKey) {
      return { key: location.href, title: "" };
    }
    if (isLivePage()) {
      const info = await liveSessionInfo();
      if (info?.key) {
        return info;
      }
      if (sessionDirectoryKey) {
        return { key: sessionDirectoryKey, title: "" };
      }
    }
    return { key: pathKey, title: "" };
  }

  function fileName(kind, extension) {
    return `${kind}-${stamp()}.${extension}`;
  }

  function openDirectoryDb() {
    return new Promise((resolve, reject) => {
      const request = indexedDB.open(DIRECTORY_DB_NAME, 1);
      request.onupgradeneeded = () => {
        request.result.createObjectStore(DIRECTORY_STORE_NAME);
      };
      request.onsuccess = () => resolve(request.result);
      request.onerror = () => reject(request.error || new Error("저장 폴더 DB 열기 실패"));
    });
  }

  async function directoryDbRequest(method, key, value) {
    const db = await openDirectoryDb();
    return new Promise((resolve, reject) => {
      const tx = db.transaction(DIRECTORY_STORE_NAME, "readwrite");
      const store = tx.objectStore(DIRECTORY_STORE_NAME);
      const request = method === "put" ? store.put(value, key) : store.get(key);
      request.onsuccess = () => resolve(request.result);
      request.onerror = () => reject(request.error || new Error("저장 폴더 DB 처리 실패"));
      tx.oncomplete = () => db.close();
      tx.onerror = () => {
        db.close();
        reject(tx.error || new Error("저장 폴더 DB 트랜잭션 실패"));
      };
    });
  }

  async function restoreDirectoryHandle() {
    if (directoryHandleLoaded) {
      return directoryHandle;
    }
    directoryHandleLoaded = true;
    try {
      directoryHandle = await directoryDbRequest("get", DIRECTORY_HANDLE_KEY);
    } catch (error) {
      console.info("MoneCapture folder restore skipped", error);
      directoryHandle = null;
    }
    return directoryHandle;
  }

  async function rememberDirectoryHandle(handle) {
    directoryHandle = handle;
    directoryHandleLoaded = true;
    directoryPermissionGranted = true;
    resetSessionDirectory();
    await directoryDbRequest("put", DIRECTORY_HANDLE_KEY, handle);
  }

  async function hasDirectoryPermission(handle, requestPermission = false) {
    if (handle === directoryHandle && directoryPermissionGranted) {
      return true;
    }
    const descriptor = { mode: "readwrite" };
    if ((await handle.queryPermission(descriptor)) === "granted") {
      if (handle === directoryHandle) {
        directoryPermissionGranted = true;
      }
      return true;
    }
    if (!requestPermission) {
      return false;
    }
    const granted = (await handle.requestPermission(descriptor)) === "granted";
    if (granted && handle === directoryHandle) {
      directoryPermissionGranted = true;
    }
    return granted;
  }

  async function chooseSaveFolder() {
    if (!canPickDirectory()) {
      throw new Error("이 브라우저는 폴더 직접 저장을 지원하지 않습니다.");
    }
    let handle;
    try {
      handle = await window.showDirectoryPicker({
        id: "mone-capture-video",
        mode: "readwrite",
      });
    } catch (error) {
      if (isAbortError(error)) {
        showStatus("폴더 선택 취소");
        return null;
      }
      throw error;
    }
    await rememberDirectoryHandle(handle);
    showStatus(`저장 폴더 선택됨: ${handle.name}`);
    updateButtons().catch(handleAsyncError);
    return handle;
  }

  async function ensureDirectoryHandle(requestPermission = false) {
    if (options.saveMode !== "folder") {
      return null;
    }
    if (!canPickDirectory()) {
      return null;
    }
    const handle = await restoreDirectoryHandle();
    if (handle && await hasDirectoryPermission(handle, requestPermission)) {
      return handle;
    }
    if (!requestPermission) {
      return null;
    }
    return chooseSaveFolder();
  }

  async function ensureSessionDirectoryHandle(rootHandle) {
    const directoryInfo = await currentSessionDirectoryInfo();
    const directoryKey = directoryInfo.key || location.href;
    if (sessionDirectoryRootHandle === rootHandle && sessionDirectoryKey === directoryKey && sessionDirectoryHandle) {
      return sessionDirectoryHandle;
    }
    const folderName = sessionFolderName(directoryInfo.title || streamTitle());
    const folderHandle = await rootHandle.getDirectoryHandle(folderName, { create: true });
    sessionDirectoryRootHandle = rootHandle;
    sessionDirectoryHandle = folderHandle;
    sessionDirectoryName = folderName;
    sessionDirectoryKey = directoryKey;
    return folderHandle;
  }

  async function prepareSaveTarget(action) {
    if (!["screenshot", "screenshot-delayed", "record"].includes(action) || options.saveMode !== "folder") {
      return;
    }
    try {
      if (await ensureDirectoryHandle(false)) {
        return;
      }
      await ensureDirectoryHandle(true);
    } catch (error) {
      if (isAbortError(error)) {
        showStatus("폴더 선택 취소");
        return;
      }
      console.info("MoneCapture folder prepare skipped", error);
      showStatus("폴더 선택이 취소되어 다운로드로 저장합니다.", true);
    }
  }

  function canvasToBlob(canvas) {
    return new Promise((resolve, reject) => {
      canvas.toBlob((blob) => {
        if (blob) {
          resolve(blob);
          return;
        }
        reject(new Error("이미지 변환 실패"));
      }, "image/png");
    });
  }

  async function acquireCanvas(width, height) {
    for (;;) {
      let slot = screenshotCanvasPool.find((item) => !item.busy && item.width === width && item.height === height);
      if (!slot) {
        slot = screenshotCanvasPool.find((item) => !item.busy);
      }
      if (!slot && screenshotCanvasPool.length < SCREENSHOT_CANVAS_POOL_LIMIT) {
        slot = {
          canvas: document.createElement("canvas"),
          context: null,
          width: 0,
          height: 0,
          busy: false,
        };
        screenshotCanvasPool.push(slot);
      }
      if (slot) {
        slot.busy = true;
        if (slot.width !== width || slot.height !== height) {
          slot.canvas.width = width;
          slot.canvas.height = height;
          slot.context = null;
          slot.width = width;
          slot.height = height;
        }
        if (!slot.context) {
          slot.context = slot.canvas.getContext("2d", {
            alpha: false,
            desynchronized: true,
          });
          if (!slot.context) {
            slot.busy = false;
            throw new Error("canvas 생성 실패");
          }
          slot.context.imageSmoothingEnabled = false;
        }
        return slot;
      }
      await new Promise((resolve) => window.setTimeout(resolve, 4));
    }
  }

  async function canvasSlotToBlob(slot) {
    try {
      return await canvasToBlob(slot.canvas);
    } finally {
      slot.busy = false;
    }
  }

  function waitMs(ms) {
    return new Promise((resolve) => window.setTimeout(resolve, ms));
  }

  function noCurrentFallbackError(message) {
    const error = new Error(message);
    error.noCurrentFallback = true;
    return error;
  }

  function clearDelayedFrameCache() {
    window.clearTimeout(delayedFrameCacheTimer);
    delayedFrameCacheTimer = 0;
    delayedFrameCacheActiveUntil = 0;
    delayedFrameCache.forEach((frame) => {
      frame.canvas.width = 0;
      frame.canvas.height = 0;
      frame.context = null;
      frame.width = 0;
      frame.height = 0;
      frame.capturedAt = 0;
      frame.mediaTime = 0;
    });
    delayedFrameCache = [];
    delayedFrameCacheIndex = 0;
  }

  function continuousCaptureIntervalForAction(action) {
    if (action === "screenshot-delayed") {
      return moneNormalizeContinuousCaptureIntervalMs(options.continuousDelayedCaptureIntervalMs);
    }
    return moneNormalizeContinuousCaptureIntervalMs(options.continuousInstantCaptureIntervalMs);
  }

  function delayedFrameCacheIntervalMs() {
    const preset = moneDelayedFrameCachePreset(options.delayedFrameCachePreset);
    if (continuousCaptureAction === "screenshot-delayed") {
      return Math.max(preset.intervalMs, continuousCaptureIntervalForAction("screenshot-delayed"));
    }
    return Math.max(preset.intervalMs, DELAYED_FRAME_CACHE_INTERVAL_MS);
  }

  function delayedFrameCacheSeconds() {
    const cacheSeconds = moneNormalizeDelayedFrameCacheSeconds(options.delayedFrameCacheSeconds);
    const delaySeconds = moneNormalizeScreenshotDelaySeconds(options.screenshotDelaySeconds);
    return Math.min(MONE_DELAYED_FRAME_CACHE_MAX_SECONDS, Math.max(cacheSeconds, delaySeconds + DELAYED_FRAME_CACHE_MARGIN_SECONDS));
  }

  function delayedFrameCacheMaxFrames(width = 0, height = 0) {
    const preset = moneDelayedFrameCachePreset(options.delayedFrameCachePreset);
    const delayMs = delayedFrameCacheSeconds() * 1000;
    const intervalMs = delayedFrameCacheIntervalMs();
    const frameBytes = width > 0 && height > 0 ? width * height * 4 : 0;
    const memoryFrames = frameBytes ? Math.max(4, Math.floor(DELAYED_FRAME_CACHE_MAX_BYTES / frameBytes)) : preset.maxFrames;
    return Math.max(4, Math.min(preset.maxFrames, memoryFrames, Math.max(4, Math.ceil(delayMs / intervalMs) + 4)));
  }

  function delayedFrameCacheSize(video) {
    const sourceWidth = video.videoWidth || Math.round(video.getBoundingClientRect().width * window.devicePixelRatio);
    const sourceHeight = video.videoHeight || Math.round(video.getBoundingClientRect().height * window.devicePixelRatio);
    const preset = moneDelayedFrameCachePreset(options.delayedFrameCachePreset);
    if (!preset.maxWidth || sourceWidth <= preset.maxWidth) {
      return { width: sourceWidth, height: sourceHeight };
    }
    return {
      width: preset.maxWidth,
      height: Math.max(4, Math.round(sourceHeight * (preset.maxWidth / sourceWidth))),
    };
  }

  function delayedFrameSlot(width, height) {
    const maxFrames = delayedFrameCacheMaxFrames(width, height);
    while (delayedFrameCache.length > maxFrames) {
      const removed = delayedFrameCache.pop();
      if (removed) {
        removed.canvas.width = 0;
        removed.canvas.height = 0;
      }
    }
    let frame = delayedFrameCache[delayedFrameCacheIndex % maxFrames];
    if (!frame) {
      const canvas = document.createElement("canvas");
      frame = {
        canvas,
        context: null,
        width: 0,
        height: 0,
        capturedAt: 0,
        mediaTime: 0,
      };
      delayedFrameCache[delayedFrameCacheIndex % maxFrames] = frame;
    }
    delayedFrameCacheIndex = (delayedFrameCacheIndex + 1) % maxFrames;
    if (frame.width !== width || frame.height !== height) {
      frame.canvas.width = width;
      frame.canvas.height = height;
      frame.context = null;
      frame.width = width;
      frame.height = height;
    }
    if (!frame.context) {
      frame.context = frame.canvas.getContext("2d", {
        alpha: false,
        desynchronized: true,
      });
      if (!frame.context) {
        throw new Error("이전 프레임 캐시 canvas 생성 실패");
      }
      frame.context.imageSmoothingEnabled = false;
    }
    return frame;
  }

  function scheduleDelayedFrameCache(video) {
    const now = Date.now();
    if (delayedFrameCacheTimer || now > delayedFrameCacheActiveUntil || now < delayedFrameCacheDisabledUntil) {
      return;
    }
    delayedFrameCacheTimer = window.setTimeout(() => {
      delayedFrameCacheTimer = 0;
      captureDelayedFrameCache(video);
    }, delayedFrameCacheIntervalMs());
  }

  function captureDelayedFrameCache(video) {
    const now = Date.now();
    if (now < delayedFrameCacheDisabledUntil) {
      scheduleDelayedFrameCache(video);
      return;
    }
    if (now > delayedFrameCacheActiveUntil || !video?.isConnected) {
      clearDelayedFrameCache();
      return;
    }
    const { width, height } = delayedFrameCacheSize(video);
    if (width >= 4 && height >= 4 && !video.seeking && !video.paused) {
      try {
        const frame = delayedFrameSlot(width, height);
        frame.context.drawImage(video, 0, 0, width, height);
        frame.capturedAt = performance.now();
        frame.mediaTime = Number(video.currentTime) || 0;
      } catch (error) {
        console.info("MoneCapture delayed frame cache skipped", error);
        delayedFrameCacheDisabledUntil = Date.now() + DELAYED_FRAME_CACHE_ERROR_BACKOFF_MS;
        clearDelayedFrameCache();
        return;
      }
    }
    if (options.screenshot && isSupportedPage() && !document.hidden && !video.paused) {
      delayedFrameCacheActiveUntil = Math.max(delayedFrameCacheActiveUntil, now + Math.max(DELAYED_FRAME_CACHE_ACTIVE_MS, delayedFrameCacheSeconds() * 1000));
    }
    scheduleDelayedFrameCache(video);
  }

  function keepDelayedFrameCacheWarm(video) {
    if (Date.now() < delayedFrameCacheDisabledUntil) {
      return;
    }
    delayedFrameCacheActiveUntil = Math.max(delayedFrameCacheActiveUntil, Date.now() + Math.max(DELAYED_FRAME_CACHE_ACTIVE_MS, delayedFrameCacheSeconds() * 1000));
    if (!delayedFrameCacheTimer) {
      captureDelayedFrameCache(video);
    }
  }

  function warmDelayedFrameCacheIfNeeded(video = findVideo()) {
    if (!options.screenshot || document.hidden || !isSupportedPage() || !video || video.paused || video.seeking) {
      return;
    }
    keepDelayedFrameCacheWarm(video);
  }

  function stopDelayedFrameWarmMonitor() {
    window.clearTimeout(delayedFrameWarmTimer);
    delayedFrameWarmTimer = 0;
  }

  function scheduleDelayedFrameWarmMonitor(delay = DELAYED_FRAME_WARM_CHECK_MS) {
    window.clearTimeout(delayedFrameWarmTimer);
    if (extensionDisposed || !isSupportedPage()) {
      return;
    }
    delayedFrameWarmTimer = window.setTimeout(() => {
      delayedFrameWarmTimer = 0;
      warmDelayedFrameCacheIfNeeded();
      scheduleDelayedFrameWarmMonitor();
    }, delay);
  }

  async function screenshotFromDelayedFrameCache(video, targetMediaTime) {
    const { width, height } = delayedFrameCacheSize(video);
    const intervalMs = delayedFrameCacheIntervalMs();
    const toleranceMs = Math.max(17, intervalMs / 2);
    const toleranceSeconds = toleranceMs / 1000;
    const oldestMediaTime = delayedFrameCache.reduce((oldest, frame) => frame.mediaTime ? Math.min(oldest, frame.mediaTime) : oldest, Number.POSITIVE_INFINITY);
    const newestMediaTime = delayedFrameCache.reduce((newest, frame) => frame.mediaTime ? Math.max(newest, frame.mediaTime) : newest, 0);
    if (!Number.isFinite(oldestMediaTime) || targetMediaTime < oldestMediaTime - toleranceSeconds || targetMediaTime > newestMediaTime + toleranceSeconds) {
      return null;
    }
    const candidates = delayedFrameCache
      .filter((frame) => frame.mediaTime && frame.width === width && frame.height === height && frame.mediaTime <= targetMediaTime + toleranceSeconds && frame.mediaTime >= targetMediaTime - Math.max(1, (intervalMs * 4) / 1000))
      .sort((left, right) => Math.abs(left.mediaTime - targetMediaTime) - Math.abs(right.mediaTime - targetMediaTime));
    const frame = candidates[0];
    if (!frame) {
      return null;
    }
    const slot = await acquireCanvas(frame.width, frame.height);
    slot.context.drawImage(frame.canvas, 0, 0, frame.width, frame.height);
    return canvasSlotToBlob(slot);
  }

  async function waitForDelayedFrameCache(video, delaySeconds, targetMediaTime) {
    const intervalMs = delayedFrameCacheIntervalMs();
    const timeoutMs = Math.min(5500, Math.max(500, (delaySeconds * 1000) + (intervalMs * 3)));
    const startedAt = performance.now();
    let notified = false;
    while (performance.now() - startedAt <= timeoutMs) {
      keepDelayedFrameCacheWarm(video);
      const cachedBlob = await screenshotFromDelayedFrameCache(video, targetMediaTime);
      if (cachedBlob) {
        return cachedBlob;
      }
      if (!notified) {
        notified = true;
        showStatus(`BACK ${delaySeconds}초 캐시 준비 중`);
      }
      await waitMs(Math.max(17, Math.min(100, intervalMs)));
    }
    return null;
  }

  function downloadBlob(blob, name) {
    const url = URL.createObjectURL(blob);
    const link = document.createElement("a");
    link.href = url;
    link.download = name;
    document.documentElement.appendChild(link);
    link.click();
    link.remove();
    window.setTimeout(() => URL.revokeObjectURL(url), 1500);
  }

  async function saveBlob(blob, name) {
    if (options.saveMode === "folder") {
      try {
        const handle = await ensureDirectoryHandle(false);
        if (handle) {
          const saveHandle = await ensureSessionDirectoryHandle(handle);
          const fileHandle = await saveHandle.getFileHandle(name, { create: true });
          const writable = await fileHandle.createWritable();
          await writable.write(blob);
          await writable.close();
          return { mode: "folder", name, folder: `${handle.name}/${sessionDirectoryName}` };
        }
      } catch (error) {
        console.info("MoneCapture folder save fallback", error);
        showStatus("폴더 저장 실패, 다운로드로 저장합니다.", true);
      }
    }
    downloadBlob(blob, name);
    return { mode: "download", name };
  }

  function enqueueScreenshotSave(blob, name) {
    pendingScreenshotSaves += 1;
    saveQueue = saveQueue
      .catch(() => {})
      .then(() => saveBlob(blob, name))
      .catch((error) => {
        showStatus(error.message || String(error), true);
        return { mode: "error", name, error };
      })
      .finally(() => {
        pendingScreenshotSaves = Math.max(0, pendingScreenshotSaves - 1);
      });
    return pendingScreenshotSaves;
  }

  function showStatus(message, isError = false) {
    let status = document.getElementById(STATUS_ID);
    if (!status) {
      status = document.createElement("div");
      status.id = STATUS_ID;
      document.documentElement.appendChild(status);
    }
    status.textContent = message;
    status.className = isError ? "mone-capture-video-status error" : "mone-capture-video-status";
    window.clearTimeout(showStatus.timer);
    showStatus.timer = window.setTimeout(() => status.remove(), 2400);
  }

  function loadImage(dataUrl) {
    return new Promise((resolve, reject) => {
      const image = new Image();
      image.onload = () => resolve(image);
      image.onerror = () => reject(new Error("탭 캡쳐 이미지 로드 실패"));
      image.src = dataUrl;
    });
  }

  function requestVisibleTab() {
    return new Promise((resolve, reject) => {
      chrome.runtime.sendMessage({ type: "mone-capture-visible-tab" }, (response) => {
        if (chrome.runtime.lastError) {
          reject(new Error(chrome.runtime.lastError.message));
          return;
        }
        if (!response?.ok || !response.dataUrl) {
          reject(new Error(response?.error || "현재 탭 캡쳐 실패"));
          return;
        }
        resolve(response.dataUrl);
      });
    });
  }

  async function screenshotFromVideo(video) {
    const width = video.videoWidth || Math.round(video.getBoundingClientRect().width * window.devicePixelRatio);
    const height = video.videoHeight || Math.round(video.getBoundingClientRect().height * window.devicePixelRatio);
    if (width < 4 || height < 4) {
      throw new Error("video 크기 없음");
    }
    const slot = await acquireCanvas(width, height);
    slot.context.drawImage(video, 0, 0, width, height);
    return canvasSlotToBlob(slot);
  }

  async function screenshotFromVisibleTab(video) {
    const rect = video.getBoundingClientRect();
    const dpr = window.devicePixelRatio || 1;
    const sx = Math.max(0, Math.round(rect.left * dpr));
    const sy = Math.max(0, Math.round(rect.top * dpr));
    const sw = Math.max(4, Math.round(rect.width * dpr));
    const sh = Math.max(4, Math.round(rect.height * dpr));
    const image = await loadImage(await requestVisibleTab());
    const width = Math.max(4, Math.min(sw, image.naturalWidth - sx));
    const height = Math.max(4, Math.min(sh, image.naturalHeight - sy));
    const slot = await acquireCanvas(width, height);
    slot.context.drawImage(image, sx, sy, slot.canvas.width, slot.canvas.height, 0, 0, slot.canvas.width, slot.canvas.height);
    return canvasSlotToBlob(slot);
  }

  function isTimeSeekable(video, time) {
    const ranges = video.seekable;
    for (let index = 0; index < ranges.length; index += 1) {
      if (time >= ranges.start(index) && time <= ranges.end(index)) {
        return true;
      }
    }
    return ranges.length === 0 && Number.isFinite(video.duration);
  }

  function waitForSeek(video, timeoutMs = SCREENSHOT_DELAY_SEEK_TIMEOUT_MS) {
    if (!video.seeking) {
      return waitForVideoFrame(video, timeoutMs);
    }
    return new Promise((resolve, reject) => {
      let frameRequest = 0;
      const timeout = window.setTimeout(() => {
        cleanup();
        reject(new Error("이전 프레임 이동 시간 초과"));
      }, timeoutMs);
      const cleanup = () => {
        window.clearTimeout(timeout);
        video.removeEventListener("seeked", onSeeked);
        if (frameRequest && typeof video.cancelVideoFrameCallback === "function") {
          video.cancelVideoFrameCallback(frameRequest);
        }
      };
      const onSeeked = () => {
        if (typeof video.requestVideoFrameCallback === "function") {
          frameRequest = video.requestVideoFrameCallback(() => {
            cleanup();
            resolve();
          });
          return;
        }
        cleanup();
        resolve();
      };
      video.addEventListener("seeked", onSeeked, { once: true });
    });
  }

  function waitForVideoFrame(video, timeoutMs = SCREENSHOT_DELAY_SEEK_TIMEOUT_MS) {
    if (typeof video.requestVideoFrameCallback !== "function") {
      return Promise.resolve();
    }
    return new Promise((resolve) => {
      let frameRequest = 0;
      const cleanup = () => {
        window.clearTimeout(timeout);
        if (frameRequest && typeof video.cancelVideoFrameCallback === "function") {
          video.cancelVideoFrameCallback(frameRequest);
        }
      };
      const timeout = window.setTimeout(() => {
        cleanup();
        resolve();
      }, timeoutMs);
      frameRequest = video.requestVideoFrameCallback(() => {
        cleanup();
        resolve();
      });
    });
  }

  async function screenshotFromDelayedVideo(video, referenceMediaTime = Number(video.currentTime)) {
    const delaySeconds = moneNormalizeScreenshotDelaySeconds(options.screenshotDelaySeconds);
    if (!Number.isFinite(referenceMediaTime) || referenceMediaTime < delaySeconds) {
      throw noCurrentFallbackError("BACK 기준 시간을 잡을 수 없습니다.");
    }
    const targetMediaTime = Math.max(0, referenceMediaTime - delaySeconds);
    keepDelayedFrameCacheWarm(video);
    const cachedBlob = await waitForDelayedFrameCache(video, delaySeconds, targetMediaTime);
    if (cachedBlob) {
      return cachedBlob;
    }
    const restoreTime = Number(video.currentTime);
    if (!isTimeSeekable(video, targetMediaTime)) {
      throw noCurrentFallbackError("BACK 캐시가 아직 준비되지 않았습니다.");
    }
    let shouldRestore = false;
    try {
      shouldRestore = true;
      if (typeof video.fastSeek === "function") {
        video.fastSeek(targetMediaTime);
      } else {
        video.currentTime = targetMediaTime;
      }
      await waitForSeek(video);
      return await screenshotFromVideo(video);
    } finally {
      if (shouldRestore && Number.isFinite(restoreTime) && isTimeSeekable(video, restoreTime)) {
        try {
          if (typeof video.fastSeek === "function") {
            video.fastSeek(restoreTime);
          } else {
            video.currentTime = restoreTime;
          }
          await waitForSeek(video).catch((error) => {
            console.info("MoneCapture delayed screenshot restore wait skipped", error);
          });
        } catch (error) {
          console.info("MoneCapture delayed screenshot restore skipped", error);
        }
      }
    }
  }

  async function captureScreenshot(delayed = false, request = {}) {
    const video = findVideo();
    if (!video) {
      throw new Error("video 태그 없음");
    }
    const referenceMediaTime = delayed && Number.isFinite(request.referenceMediaTime) ? request.referenceMediaTime : Number(video.currentTime);
    let blob;
    try {
      blob = delayed
        ? await (delayedScreenshotQueue = delayedScreenshotQueue.catch(() => {}).then(() => screenshotFromDelayedVideo(video, referenceMediaTime)))
        : await screenshotFromVideo(video);
    } catch (error) {
      if (delayed && error?.noCurrentFallback) {
        throw error;
      }
      console.info("MoneCapture screenshot fallback", error);
      blob = await screenshotFromVisibleTab(video);
    }
    const pendingSaves = enqueueScreenshotSave(blob, fileName("screenshot", "png"));
    return {
      mode: "queued",
      pendingSaves,
      width: video.videoWidth || Math.round(video.getBoundingClientRect().width),
      height: video.videoHeight || Math.round(video.getBoundingClientRect().height),
    };
  }

  function createMediaRecorder(stream, recordOptions) {
    const baseOptions = {
      videoBitsPerSecond: recordOptions.bitrate,
    };
    for (const mimeType of recordOptions.mimeTypes) {
      if (!MediaRecorder.isTypeSupported(mimeType)) {
        continue;
      }
      try {
        return {
          recorder: new MediaRecorder(stream, { ...baseOptions, mimeType }),
          mimeType,
        };
      } catch (error) {
        console.info("MoneCapture recorder fallback", mimeType, error);
      }
    }
    return {
      recorder: new MediaRecorder(stream, baseOptions),
      mimeType: "",
    };
  }

  async function toggleRecord() {
    if (recorder && recorder.state !== "inactive") {
      recorder.stop();
      return { recording: false };
    }
    const video = findVideo();
    if (!video) {
      throw new Error("video 태그 없음");
    }
    const stream = video.captureStream?.() || video.mozCaptureStream?.();
    if (!stream) {
      throw new Error("이 브라우저는 video.captureStream을 지원하지 않습니다.");
    }
    if (typeof MediaRecorder !== "function") {
      stream.getTracks().forEach((track) => track.stop());
      throw new Error("이 브라우저는 MediaRecorder를 지원하지 않습니다.");
    }
    recordChunks = [];
    recordBufferedBytes = 0;
    const recordOptions = moneEffectiveRecordOptions(options);
    let createdRecorder;
    try {
      createdRecorder = createMediaRecorder(stream, recordOptions);
    } catch (error) {
      stream.getTracks().forEach((track) => track.stop());
      throw error;
    }
    const mimeType = createdRecorder.mimeType;
    recorder = createdRecorder.recorder;
    const activeRecorder = recorder;
    recorder.ondataavailable = (event) => {
      if (event.data && event.data.size > 0) {
        recordChunks.push(event.data);
        recordBufferedBytes += event.data.size;
        if (recordBufferedBytes > RECORD_MAX_BUFFER_BYTES && activeRecorder.state === "recording") {
          showStatus("녹화 버퍼 한도 도달, 자동 저장합니다.", true);
          activeRecorder.stop();
        }
      }
    };
    recorder.onstop = async () => {
      window.clearTimeout(recordLimitTimer);
      recordLimitTimer = 0;
      stopRecordOverlay();
      const recordMimeType = activeRecorder.mimeType || mimeType || "video/webm";
      const blob = new Blob(recordChunks, { type: recordMimeType });
      recordChunks = [];
      recordBufferedBytes = 0;
      stream.getTracks().forEach((track) => track.stop());
      try {
        const saved = await saveBlob(blob, fileName("record", moneRecordingExtension(recordMimeType)));
        showStatus(saved.mode === "folder" ? `녹화 폴더 저장 완료: ${saved.folder}` : "녹화 다운로드 저장 완료");
      } catch (error) {
        showStatus(error.message || String(error), true);
      }
      updateButtons().catch(handleAsyncError);
    };
    recorder.start(recordOptions.chunkMs);
    recordLimitTimer = window.setTimeout(() => {
      if (activeRecorder.state === "recording") {
        showStatus("녹화 5분 한도 도달, 자동 저장합니다.", true);
        activeRecorder.stop();
      }
    }, RECORD_MAX_DURATION_MS);
    startRecordOverlay();
    updateButtons().catch(handleAsyncError);
    return { recording: true };
  }

  function seek(seconds) {
    const video = findVideo();
    if (!video) {
      throw new Error("video 태그 없음");
    }
    video.currentTime = Math.max(0, video.currentTime + seconds);
    showSeekOverlay(seconds);
    return { currentTime: video.currentTime };
  }

  function livePlaybackState(video) {
    if (!video?.seekable?.length) {
      return null;
    }
    const index = video.seekable.length - 1;
    const start = video.seekable.start(index);
    const edge = video.seekable.end(index);
    const latency = edge - video.currentTime;
    if (![start, edge, latency].every(Number.isFinite) || edge <= start || latency < 0) {
      return null;
    }
    return { start, edge, latency };
  }

  function stopLowLatency(resetRate = true) {
    const shouldUpdate = lowLatencyEnabled;
    window.clearTimeout(lowLatencyTimer);
    lowLatencyTimer = 0;
    lowLatencyEnabled = false;
    lowLatencyLastNoticeAt = 0;
    if (resetRate) {
      const video = findVideo();
      if (video) {
        video.playbackRate = normalPlaybackRate || 1;
      }
    }
    if (shouldUpdate) {
      updateButtons().catch(handleAsyncError);
    }
  }

  function scheduleLowLatencyTick() {
    window.clearTimeout(lowLatencyTimer);
    lowLatencyTimer = window.setTimeout(applyLowLatency, LOW_LATENCY_CHECK_MS);
  }

  function targetLiveLatencySeconds() {
    return LOW_LATENCY_TARGET_SECONDS;
  }

  function applyLowLatency() {
    if (!lowLatencyEnabled || !isLivePage()) {
      stopLowLatency();
      return;
    }
    const video = findVideo();
    if (!video) {
      scheduleLowLatencyTick();
      return;
    }
    const state = livePlaybackState(video);
    if (!state) {
      video.playbackRate = normalPlaybackRate || 1;
      scheduleLowLatencyTick();
      return;
    }
    if (!video.paused) {
      const targetLatency = targetLiveLatencySeconds();
      const now = Date.now();
      const canNotice = now - lowLatencyLastNoticeAt >= LOW_LATENCY_NOTICE_COOLDOWN_MS;
      video.playbackRate = normalPlaybackRate || 1;
      if (canNotice && state.latency > targetLatency + LOW_LATENCY_SPEEDUP_SECONDS) {
        lowLatencyLastNoticeAt = now;
        showStatus(`라이브 딜레이 ${Math.round(state.latency)}초 · 자동 보정 대기`);
      }
    }
    scheduleLowLatencyTick();
  }

  function toggleLowLatency() {
    if (!isLivePage()) {
      throw new Error("라이브 방송 페이지에서만 사용할 수 있습니다.");
    }
    const video = findVideo();
    if (!video) {
      throw new Error("video 태그 없음");
    }
    if (lowLatencyEnabled) {
      stopLowLatency();
      showStatus("딜레이 최소화 끔");
      return { lowLatency: false };
    }
    normalPlaybackRate = Number(video.playbackRate) || 1;
    lowLatencyEnabled = true;
    video.playbackRate = normalPlaybackRate || 1;
    scheduleLowLatencyTick();
    updateButtons().catch(handleAsyncError);
    showStatus("딜레이 감시 켬");
    return { lowLatency: true };
  }

  function showSeekOverlay(seconds) {
    let overlay = document.getElementById("mone-capture-seek-overlay");
    if (!overlay) {
      overlay = document.createElement("div");
      overlay.id = "mone-capture-seek-overlay";
      document.documentElement.appendChild(overlay);
    }
    overlay.textContent = `${seconds > 0 ? "+" : ""}${seconds}초`;
    overlay.className = seconds > 0 ? "right" : "left";
    window.clearTimeout(showSeekOverlay.timer);
    showSeekOverlay.timer = window.setTimeout(() => overlay.remove(), 900);
  }

  function startRecordOverlay() {
    recordStartedAt = Date.now();
    let overlay = document.getElementById(OVERLAY_ID);
    if (!overlay) {
      overlay = document.createElement("div");
      overlay.id = OVERLAY_ID;
      document.documentElement.appendChild(overlay);
    }
    const tick = () => {
      const elapsed = Math.floor((Date.now() - recordStartedAt) / 1000);
      const minutes = String(Math.floor(elapsed / 60)).padStart(2, "0");
      const seconds = String(elapsed % 60).padStart(2, "0");
      overlay.textContent = `REC ${minutes}:${seconds} / 05:00`;
      recordTimer = window.setTimeout(tick, 500);
    };
    tick();
  }

  function stopRecordOverlay() {
    window.clearTimeout(recordTimer);
    window.clearTimeout(recordLimitTimer);
    recordLimitTimer = 0;
    document.getElementById(OVERLAY_ID)?.remove();
  }

  function makeHideIcon() {
    const svg = document.createElementNS("http://www.w3.org/2000/svg", "svg");
    svg.setAttribute("viewBox", "0 0 24 24");
    svg.setAttribute("aria-hidden", "true");

    const eye = document.createElementNS("http://www.w3.org/2000/svg", "path");
    eye.setAttribute("d", "M10.6 10.6A2 2 0 0 0 13.4 13.4");

    const shape = document.createElementNS("http://www.w3.org/2000/svg", "path");
    shape.setAttribute("d", "M9.5 5.4A9.5 9.5 0 0 1 21 12a10.6 10.6 0 0 1-2.1 3.2");

    const shapeHidden = document.createElementNS("http://www.w3.org/2000/svg", "path");
    shapeHidden.setAttribute("d", "M6.4 6.4A10.6 10.6 0 0 0 3 12a10.8 10.8 0 0 0 12.7 5.7");

    const slash = document.createElementNS("http://www.w3.org/2000/svg", "path");
    slash.setAttribute("d", "M3 3l18 18");

    svg.append(eye, shape, shapeHidden, slash);
    return svg;
  }

  function makeButton(action, label, title, icon = "") {
    const button = document.createElement("button");
    button.type = "button";
    button.dataset.moneAction = action;
    button.className = "mone-capture-tool-button";
    button.title = title;
    button.setAttribute("aria-label", title);
    if (icon === "hide") {
      button.classList.add("icon");
      button.appendChild(makeHideIcon());
    } else {
      button.textContent = label;
    }
    button.addEventListener("click", (event) => {
      event.preventDefault();
      event.stopPropagation();
      runAction(action).catch(handleAsyncError);
    });
    return button;
  }

  function removeToolbar() {
    document.getElementById(ROOT_ID)?.remove();
    const host = document.getElementById(HOST_ID);
    host?.parentElement?.classList.remove("mone-capture-toolbar-row");
    host?.remove();
  }

  async function injectButtons() {
    if (extensionDisposed) {
      return;
    }
    if (!isSupportedPage()) {
      handleUnsupportedPage();
      return;
    }
    if (!isLivePage() && lowLatencyEnabled) {
      stopLowLatency();
    }
    await ensureOptionsLoaded();
    const video = findVideo();
    if (!video) {
      removeToolbar();
      return;
    }
    warmDelayedFrameCacheIfNeeded(video);
    if (!options.toolbarVisible) {
      removeToolbar();
      return;
    }
    const existing = document.getElementById(ROOT_ID);
    if (existing) {
      attachToolbar(existing, video);
      await updateButtons();
      return;
    }
    let root = document.getElementById(ROOT_ID);
    if (!root) {
      root = document.createElement("div");
      root.id = ROOT_ID;
    }
    root.innerHTML = "";
    if (options.lowLatency && isLivePage()) root.appendChild(makeButton("low-latency", "LAT", "방송 딜레이 감시"));
    if (options.screenshot) root.appendChild(makeButton("screenshot", "SHOT", `스크린샷 (${moneShortcutLabel(options.screenshotKey)})`));
    if (options.screenshot) root.appendChild(makeButton("screenshot-delayed", "BACK", `이전 캡쳐 (${moneNormalizeScreenshotDelaySeconds(options.screenshotDelaySeconds)}초 전)`));
    if (options.record) root.appendChild(makeButton("record", recorder?.state === "recording" ? "STOP" : "REC", `녹화 (${moneShortcutLabel(options.recordKey)})`));
    root.appendChild(makeButton("hide-toolbar", "", "버튼 숨기기", "hide"));

    attachToolbar(root, video);
    updateButtons().catch(handleAsyncError);
  }

  async function updateButtons() {
    if (extensionDisposed) {
      return;
    }
    if (!isSupportedPage()) {
      handleUnsupportedPage();
      return;
    }
    const root = document.getElementById(ROOT_ID);
    if (!root) {
      return;
    }
    attachToolbar(root);
    const recordButton = root.querySelector("[data-mone-action='record']");
    if (recordButton) {
      recordButton.textContent = recorder?.state === "recording" ? "STOP" : "REC";
      recordButton.classList.toggle("recording", recorder?.state === "recording");
    }
    const lowLatencyButton = root.querySelector("[data-mone-action='low-latency']");
    if (lowLatencyButton) {
      lowLatencyButton.classList.toggle("active", lowLatencyEnabled);
    }
  }

  async function runAction(action) {
    try {
      if (!isSupportedPage()) {
        throw new Error("CHZZK 라이브/비디오 페이지에서만 사용할 수 있습니다.");
      }
      const isCaptureAction = action === "screenshot" || action === "screenshot-delayed";
      if (!isCaptureAction && nonCaptureActionRunning === action) {
        return { skipped: true };
      }
      if (!isCaptureAction) {
        nonCaptureActionRunning = action;
      }
      let result;
      if (action === "save-folder") {
        const handle = await chooseSaveFolder();
        return handle ? { folder: handle.name } : { canceled: true };
      }
      if (action === "hide-toolbar") {
        await moneSaveOptions({ ...(await moneLoadOptions()), toolbarVisible: false });
        removeToolbar();
        showStatus("화면 버튼 숨김");
        return { hidden: true };
      }
      let delayedReferenceMediaTime = null;
      if (action === "screenshot-delayed") {
        const video = findVideo();
        delayedReferenceMediaTime = Number(video?.currentTime);
        warmDelayedFrameCacheIfNeeded(video);
      }
      await prepareSaveTarget(action);
      if (action !== "screenshot" && action !== "screenshot-delayed") {
        await loadOptions();
      }
      if (action === "screenshot") result = await captureScreenshot(false);
      else if (action === "screenshot-delayed") result = await captureScreenshot(true, { referenceMediaTime: delayedReferenceMediaTime });
      else if (action === "record") result = await toggleRecord();
      else if (action === "low-latency") result = toggleLowLatency();
      else if (action === "seek-left") result = seek(-5);
      else if (action === "seek-right") result = seek(5);
      else throw new Error(`알 수 없는 기능: ${action}`);
      if (action === "screenshot" || action === "screenshot-delayed") {
        showStatus(`스크린샷 캡쳐: ${result.width}x${result.height}${result.pendingSaves > 1 ? ` · 저장 대기 ${result.pendingSaves}` : ""}`);
      }
      return result || { ok: true };
    } catch (error) {
      if (!isAbortError(error) && !moneIsExtensionContextInvalidated(error)) {
        showStatus(error.message || String(error), true);
      }
      throw error;
    } finally {
      if (nonCaptureActionRunning === action) {
        nonCaptureActionRunning = "";
      }
    }
  }

  function stopContinuousCapture() {
    window.clearTimeout(continuousCaptureTimer);
    continuousCaptureAction = "";
    continuousCaptureKey = "";
    continuousCaptureTimer = 0;
    continuousCaptureRunning = false;
    pressedCaptureKeys.clear();
    mixedCaptureHandled = false;
  }

  function captureShortcutCodeForAction(action) {
    if (action === "screenshot-delayed") {
      return options.delayedScreenshotKey;
    }
    if (action === "screenshot") {
      return options.screenshotKey;
    }
    return "";
  }

  function isOtherCaptureKeyPressed(action) {
    const ownKey = captureShortcutCodeForAction(action);
    const otherKey = action === "screenshot" ? options.delayedScreenshotKey : options.screenshotKey;
    return Boolean(otherKey && ownKey !== otherKey && pressedCaptureKeys.has(otherKey));
  }

  function scheduleContinuousCapture() {
    window.clearTimeout(continuousCaptureTimer);
    if (!continuousCaptureAction) {
      return;
    }
    const intervalMs = continuousCaptureIntervalForAction(continuousCaptureAction);
    const video = findVideo();
    const delayMs = video && typeof video.requestVideoFrameCallback === "function" && intervalMs <= MONE_CONTINUOUS_CAPTURE_MIN_INTERVAL_MS ? 0 : intervalMs;
    continuousCaptureTimer = window.setTimeout(() => {
      continuousCaptureTimer = 0;
      runContinuousCaptureTick();
    }, delayMs);
  }

  function waitForContinuousVideoFrame(action) {
    const video = findVideo();
    const intervalMs = continuousCaptureIntervalForAction(action);
    if (!video || typeof video.requestVideoFrameCallback !== "function") {
      return new Promise((resolve) => window.setTimeout(resolve, intervalMs));
    }
    return new Promise((resolve) => {
      let frameRequest = 0;
      const cleanup = () => {
        window.clearTimeout(timeout);
        if (frameRequest && typeof video.cancelVideoFrameCallback === "function") {
          video.cancelVideoFrameCallback(frameRequest);
        }
      };
      const timeout = window.setTimeout(() => {
        cleanup();
        resolve();
      }, Math.max(intervalMs * 2, 34));
      frameRequest = video.requestVideoFrameCallback(() => {
        cleanup();
        resolve();
      });
    });
  }

  async function runContinuousCaptureTick() {
    const action = continuousCaptureAction;
    if (!action || continuousCaptureRunning) {
      scheduleContinuousCapture();
      return;
    }
    continuousCaptureRunning = true;
    try {
      await waitForContinuousVideoFrame(action);
      await runAction(action);
    } catch (error) {
      handleAsyncError(error);
    } finally {
      continuousCaptureRunning = false;
      scheduleContinuousCapture();
    }
  }

  function scheduleContinuousCaptureStart(action, key) {
    window.clearTimeout(continuousCaptureTimer);
    continuousCaptureTimer = window.setTimeout(() => {
      continuousCaptureTimer = 0;
      if (continuousCaptureAction !== action || continuousCaptureKey !== key || !pressedCaptureKeys.has(key) || isOtherCaptureKeyPressed(action)) {
        stopContinuousCapture();
        return;
      }
      runContinuousCaptureTick();
    }, moneNormalizeContinuousCaptureStartDelayMs(options.continuousCaptureStartDelayMs));
  }

  function startContinuousCapture(event, action) {
    event.preventDefault();
    event.stopPropagation();
    if (isOtherCaptureKeyPressed(action)) {
      stopContinuousCapture();
      if (!event.repeat && !mixedCaptureHandled) {
        mixedCaptureHandled = true;
        runAction(action).catch(handleAsyncError);
      }
      return;
    }
    if (!options.continuousCapture) {
      if (!event.repeat) {
        runAction(action).catch(handleAsyncError);
      }
      return;
    }
    const key = moneEventCode(event);
    if (continuousCaptureAction === action && continuousCaptureKey === key) {
      return;
    }
    stopContinuousCapture();
    continuousCaptureAction = action;
    continuousCaptureKey = key;
    runAction(action).catch(handleAsyncError);
    scheduleContinuousCaptureStart(action, key);
  }

  function handleShortcut(event) {
    if (!isSupportedPage()) {
      return;
    }
    if (event.isComposing || event.altKey || event.ctrlKey || event.metaKey) {
      return;
    }
    const run = (action, continuous = false) => {
      event.preventDefault();
      event.stopPropagation();
      if (continuous) {
        pressedCaptureKeys.add(moneEventCode(event));
        startContinuousCapture(event, action);
        return;
      }
      runAction(action).catch(handleAsyncError);
    };
    if (options.screenshot && moneShortcutMatches(event, options.screenshotKey)) run("screenshot", true);
    else if (options.screenshot && moneShortcutMatches(event, options.delayedScreenshotKey)) run("screenshot-delayed", true);
    else if (options.record && moneShortcutMatches(event, options.recordKey)) run("record");
    else if (options.seek && moneShortcutMatches(event, options.seekLeftKey)) run("seek-left");
    else if (options.seek && moneShortcutMatches(event, options.seekRightKey)) run("seek-right");
  }

  function handleShortcutKeyup(event) {
    const code = moneEventCode(event);
    pressedCaptureKeys.delete(code);
    if (pressedCaptureKeys.size === 0) {
      mixedCaptureHandled = false;
    }
    if (continuousCaptureKey && code === continuousCaptureKey) {
      event.preventDefault();
      event.stopPropagation();
      stopContinuousCapture();
    }
  }

  function isRelevantElement(element) {
    if (!(element instanceof Element)) {
      return false;
    }
    return element.id === ROOT_ID ||
      element.id === HOST_ID ||
      element.matches("video, h2[class*='video_information_title'], [class*='video_information_row']");
  }

  function hasRelevantElement(node) {
    if (!(node instanceof Element)) {
      return false;
    }
    return isRelevantElement(node) ||
      Boolean(node.querySelector("video, h2[class*='video_information_title'], [class*='video_information_row'], #" + ROOT_ID + ", #" + HOST_ID));
  }

  function shouldHandleMutations(mutations) {
    if (!isSupportedPage()) {
      handleUnsupportedPage();
      return false;
    }
    if (!options.toolbarVisible) {
      return false;
    }
    return mutations.some((mutation) => {
      if (isRelevantElement(mutation.target)) {
        return true;
      }
      return Array.from(mutation.addedNodes).some(hasRelevantElement) ||
        Array.from(mutation.removedNodes).some(hasRelevantElement);
    });
  }

  function scheduleInjection(delay = INJECTION_DELAY_MS) {
    if (extensionDisposed || injectTimer) {
      return;
    }
    const timeoutDelay = Number.isFinite(delay) ? delay : INJECTION_DELAY_MS;
    injectTimer = window.setTimeout(() => {
      injectTimer = 0;
      injectButtons().catch(handleAsyncError);
    }, timeoutDelay);
  }

  function handleMutations(mutations) {
    if (shouldHandleMutations(mutations)) {
      scheduleInjection();
    }
  }

  function requestToolbarPosition() {
    if (extensionDisposed || !isSupportedPage() || options.toolbarPlacement === "info" || positionRaf) {
      return;
    }
    const root = document.getElementById(ROOT_ID);
    if (!root || !root.classList.contains("floating")) {
      return;
    }
    positionRaf = window.requestAnimationFrame(() => {
      positionRaf = 0;
      positionToolbar(root);
    });
  }

  function ensureShortcutListeners() {
    if (extensionDisposed || !isSupportedPage()) {
      return;
    }
    document.addEventListener("keydown", handleShortcut, true);
    document.addEventListener("keyup", handleShortcutKeyup, true);
    shortcutAttached = true;
  }

  function stopUiHealthCheck() {
    window.clearTimeout(uiHealthTimer);
    uiHealthTimer = 0;
  }

  function scheduleUiHealthCheck(delay = UI_HEALTH_CHECK_MS) {
    window.clearTimeout(uiHealthTimer);
    if (extensionDisposed || !isSupportedPage()) {
      return;
    }
    uiHealthTimer = window.setTimeout(() => {
      uiHealthTimer = 0;
      runUiHealthCheck().catch(handleAsyncError);
    }, delay);
  }

  async function runUiHealthCheck() {
    if (extensionDisposed || !isSupportedPage()) {
      handleUnsupportedPage();
      return;
    }
    ensureShortcutListeners();
    await ensureOptionsLoaded();
    const root = document.getElementById(ROOT_ID);
    const host = document.getElementById(HOST_ID);
    const needsToolbarRepair = options.toolbarVisible && findVideo() && (!root || !root.isConnected || (host && !host.isConnected));
    if (needsToolbarRepair) {
      scheduleInjection(0);
    }
    scheduleDelayedFrameWarmMonitor();
    scheduleUiHealthCheck();
  }

  chrome.runtime.onMessage.addListener((message, _sender, sendResponse) => {
    if (!message || message.type !== "mone-action") {
      return false;
    }
    runAction(message.action)
      .then((result) => sendResponse({ ok: true, result }))
      .catch((error) => {
        handleAsyncError(error);
        sendResponse({ ok: false, error: error.message || String(error) });
      });
    return true;
  });

  loadOptions()
    .then(() => {
      if (extensionDisposed || !isSupportedPage()) {
        handleUnsupportedPage();
        return;
      }
      ensureShortcutListeners();
      scheduleInjection();
      scheduleDelayedFrameWarmMonitor();
      scheduleUiHealthCheck(0);
      warmDelayedFrameCacheIfNeeded();
    })
    .catch(handleAsyncError);

  chrome.storage.onChanged.addListener((changes, areaName) => {
    if (areaName !== "local") {
      return;
    }
    if (changes[MONE_OPTIONS_KEY]) {
      removeToolbar();
      clearDelayedFrameCache();
      loadOptions().then(() => {
        if (!options.lowLatency && lowLatencyEnabled) {
          stopLowLatency();
        }
        if (isSupportedPage()) {
          ensureShortcutListeners();
          scheduleInjection();
          scheduleDelayedFrameWarmMonitor();
          scheduleUiHealthCheck(0);
        } else {
          stopDelayedFrameWarmMonitor();
          stopUiHealthCheck();
        }
      }).catch(handleAsyncError);
    }
  });

  mutationObserver = new MutationObserver(handleMutations);
  mutationObserver.observe(document.documentElement, { childList: true, subtree: true });
  installUrlChangeHooks();
  window.addEventListener("popstate", handleUrlChange);
  window.addEventListener("pageshow", () => {
    ensureShortcutListeners();
    scheduleInjection();
    scheduleUiHealthCheck(0);
  });
  window.addEventListener("resize", scheduleInjection);
  window.addEventListener("scroll", requestToolbarPosition, { passive: true });
  window.addEventListener("blur", stopContinuousCapture);
  document.addEventListener("visibilitychange", () => {
    if (document.hidden) {
      stopContinuousCapture();
      stopDelayedFrameWarmMonitor();
      stopUiHealthCheck();
      clearDelayedFrameCache();
      return;
    }
    ensureShortcutListeners();
    scheduleInjection();
    scheduleDelayedFrameWarmMonitor(0);
    scheduleUiHealthCheck(0);
    warmDelayedFrameCacheIfNeeded();
  });
})();
