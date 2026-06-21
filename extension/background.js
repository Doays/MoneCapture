chrome.runtime.onMessage.addListener((message, sender, sendResponse) => {
  if (!message) {
    return false;
  }

  if (message.type === "mone-open-options") {
    chrome.runtime.openOptionsPage(() => {
      if (chrome.runtime.lastError) {
        sendResponse({ ok: false, error: chrome.runtime.lastError.message });
        return;
      }
      sendResponse({ ok: true });
    });
    return true;
  }

  if (message.type === "mone-latency-badge") {
    const tabId = sender.tab?.id;
    if (!tabId) {
      sendResponse({ ok: false, error: "활성 탭을 찾을 수 없습니다." });
      return false;
    }
    const text = String(message.text || "").slice(0, 4);
    const color = message.color || "#1f6feb";
    chrome.action.setBadgeText({ tabId, text }, () => {
      if (chrome.runtime.lastError) {
        sendResponse({ ok: false, error: chrome.runtime.lastError.message });
        return;
      }
      chrome.action.setBadgeBackgroundColor({ tabId, color }, () => {
        if (chrome.runtime.lastError) {
          sendResponse({ ok: false, error: chrome.runtime.lastError.message });
          return;
        }
        sendResponse({ ok: true });
      });
    });
    return true;
  }

  if (message.type !== "mone-capture-visible-tab") {
    return false;
  }

  const windowId = sender.tab && sender.tab.windowId;
  chrome.tabs.captureVisibleTab(windowId, { format: "png" }, (dataUrl) => {
    if (chrome.runtime.lastError) {
      sendResponse({ ok: false, error: chrome.runtime.lastError.message });
      return;
    }
    sendResponse({ ok: true, dataUrl });
  });
  return true;
});
