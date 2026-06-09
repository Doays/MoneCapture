const statusEl = document.getElementById("status");
let currentOptions = { ...MONE_DEFAULT_OPTIONS };
let pendingShortcut = null;

function setStatus(message) {
  statusEl.textContent = message;
}

function isSupportedChzzkUrl(url) {
  try {
    const parsed = new URL(url);
    return parsed.origin === "https://chzzk.naver.com" &&
      (parsed.pathname.startsWith("/live/") || parsed.pathname.startsWith("/video/"));
  } catch {
    return false;
  }
}

async function targetTab() {
  const activeTabs = await new Promise((resolve) => {
    chrome.tabs.query({ active: true, currentWindow: true }, resolve);
  });
  if (isSupportedChzzkUrl(activeTabs[0]?.url)) {
    return activeTabs[0];
  }
  const tabs = await new Promise((resolve) => {
    chrome.tabs.query({ currentWindow: true }, resolve);
  });
  return tabs
    .filter((tab) => isSupportedChzzkUrl(tab.url))
    .sort((left, right) => (right.lastAccessed || 0) - (left.lastAccessed || 0))[0];
}

async function sendAction(action) {
  const tab = await targetTab();
  if (!tab?.id) {
    throw new Error("CHZZK 라이브/비디오 탭 없음");
  }
  return new Promise((resolve, reject) => {
    chrome.tabs.sendMessage(tab.id, { type: "mone-action", action }, (response) => {
      if (chrome.runtime.lastError) {
        reject(new Error(chrome.runtime.lastError.message));
        return;
      }
      resolve(response);
    });
  });
}

async function saveCurrentOptions(message = "저장됨") {
  await moneSaveOptions(currentOptions);
  currentOptions = await moneLoadOptions();
  renderFeatureOptions();
  renderShortcuts();
  setStatus(message);
}

function renderFeatureOptions() {
  document.querySelectorAll("[data-option]").forEach((input) => {
    const key = input.dataset.option;
    if (input.type === "checkbox") {
      input.checked = Boolean(currentOptions[key]);
    } else {
      input.value = currentOptions[key];
    }
  });
}

function renderShortcuts() {
  document.querySelectorAll("[data-shortcut]").forEach((button) => {
    const key = button.dataset.shortcut;
    button.textContent = pendingShortcut === key ? "키 입력 중..." : moneShortcutLabel(currentOptions[key]);
    button.classList.toggle("recording", pendingShortcut === key);
  });
}

document.querySelectorAll("[data-option]").forEach((input) => {
  input.addEventListener("change", async () => {
    const key = input.dataset.option;
    currentOptions[key] = input.type === "checkbox" ? input.checked : input.type === "number" ? Number(input.value) : input.value;
    await saveCurrentOptions("옵션 저장됨");
  });
});

document.querySelectorAll("[data-shortcut]").forEach((button) => {
  button.addEventListener("click", () => {
    pendingShortcut = button.dataset.shortcut;
    renderShortcuts();
    setStatus("원하는 키를 누르세요. Esc는 비우기입니다.");
  });
});

document.addEventListener("keydown", async (event) => {
  if (!pendingShortcut) {
    return;
  }
  event.preventDefault();
  event.stopPropagation();
  const value = moneShortcutFromEvent(event);
  if (value === null) {
    return;
  }
  currentOptions[pendingShortcut] = value;
  pendingShortcut = null;
  renderShortcuts();
  await saveCurrentOptions(value ? "단축키 저장됨" : "단축키 비움");
}, true);

document.getElementById("reset").addEventListener("click", async () => {
  currentOptions = { ...MONE_DEFAULT_OPTIONS };
  renderFeatureOptions();
  renderShortcuts();
  await saveCurrentOptions("기본값 복원됨");
});

document.getElementById("select-folder").addEventListener("click", async () => {
  try {
    const response = await sendAction("save-folder");
    if (!response?.ok) {
      throw new Error(response?.error || "저장 폴더 선택 실패");
    }
    setStatus(response.result?.canceled ? "폴더 선택 취소" : "저장 폴더 선택됨");
  } catch (error) {
    setStatus(error.message || String(error));
  }
});

moneLoadOptions()
  .then((options) => {
    currentOptions = options;
    renderFeatureOptions();
    renderShortcuts();
  })
  .catch((error) => setStatus(error.message || String(error)));
