const statusEl = document.getElementById("status");

function setStatus(message) {
  statusEl.textContent = message;
}

async function activeTab() {
  const tabs = await new Promise((resolve) => {
    chrome.tabs.query({ active: true, currentWindow: true }, resolve);
  });
  return tabs[0];
}

async function sendAction(action) {
  const tab = await activeTab();
  if (!tab?.id) {
    throw new Error("활성 탭 없음");
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

async function loadOptions() {
  return moneLoadOptions();
}

async function saveOption(name, value) {
  const options = await loadOptions();
  options[name] = value;
  await moneSaveOptions(options);
}

async function renderOptions() {
  const options = await loadOptions();
  document.querySelectorAll("[data-option]").forEach((input) => {
    const name = input.dataset.option;
    if (input.type === "checkbox") {
      input.checked = Boolean(options[name]);
    } else {
      input.value = options[name];
    }
  });
}

async function renderFavorites() {
  const favorites = await moneLoadFavorites();
  const box = document.getElementById("favorites");
  box.innerHTML = "";
  if (!favorites.length) {
    box.textContent = "없음";
    return;
  }
  favorites.forEach((item) => {
    const link = document.createElement("a");
    link.className = "favorite";
    link.href = item.url;
    link.textContent = `${item.title || item.url} · ${moneNotificationLabel(item)}`;
    link.addEventListener("click", (event) => {
      event.preventDefault();
      chrome.tabs.create({ url: item.url });
    });
    box.appendChild(link);
  });
}

document.querySelectorAll("[data-action]").forEach((button) => {
  button.addEventListener("click", async () => {
    try {
      const response = await sendAction(button.dataset.action);
      if (!response?.ok) {
        throw new Error(response?.error || "실행 실패");
      }
      setStatus(button.dataset.action === "save-folder" && response.result?.canceled ? "폴더 선택 취소" : "완료");
      await renderFavorites();
    } catch (error) {
      setStatus(error.message || String(error));
    }
  });
});

document.querySelectorAll("[data-option]").forEach((input) => {
  input.addEventListener("change", async () => {
    const value = input.type === "checkbox" ? input.checked : input.type === "number" ? Number(input.value) : input.value;
    await saveOption(input.dataset.option, value);
    await renderOptions();
    setStatus("옵션 저장");
  });
});

document.getElementById("open-options").addEventListener("click", () => {
  chrome.runtime.openOptionsPage();
});

renderOptions().catch((error) => setStatus(error.message || String(error)));
renderFavorites().catch((error) => setStatus(error.message || String(error)));
