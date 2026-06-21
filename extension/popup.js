const statusEl = document.getElementById("status");
const latencyStatusEl = document.getElementById("latency-status");
const latencyDebugListEl = document.getElementById("latency-debug-list");

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

async function requestStatus() {
  const tab = await activeTab();
  if (!tab?.id) {
    throw new Error("활성 탭 없음");
  }
  return new Promise((resolve, reject) => {
    chrome.tabs.sendMessage(tab.id, { type: "mone-status" }, (response) => {
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

function formatSeconds(value) {
  const number = Number(value);
  return Number.isFinite(number) ? `${number.toFixed(1)}초` : "-";
}

function formatCount(value) {
  const number = Number(value);
  return Number.isFinite(number) ? String(Math.round(number)) : "0";
}

function renderLatencyDebug(latency) {
  if (!latencyDebugListEl) {
    return;
  }
  if (!latency?.available) {
    latencyDebugListEl.replaceChildren();
    return;
  }
  const stats = latency.stats || {};
  const rows = [
    ["실제 목표", formatSeconds(latency.targetSeconds)],
    ["설정 목표", formatSeconds(latency.configuredTargetSeconds)],
    ["확인 간격", formatSeconds(latency.checkSeconds)],
    ["현재 배속", latency.playbackRate ? `${Number(latency.playbackRate).toFixed(2)}x` : "-"],
    ["제어 상태", latency.phase || "-"],
    ["최근 동작", stats.lastReason ? `${stats.lastAction} · ${stats.lastReason}` : (stats.lastAction || "-")],
    ["체크", formatCount(stats.ticks)],
    ["위치 보정", formatCount(stats.seekCount)],
    ["배속 보정", formatCount(stats.rateCorrectionCount)],
    ["안정화", formatCount(stats.backoffCount)],
    ["사용자 이동", formatCount(stats.userPauseCount)],
    ["화질 시도", `${formatCount(stats.qualityAttemptCount)} / ${formatCount(stats.qualitySelectCount)}`],
    ["버퍼 이벤트", `${formatCount(stats.waitingCount)} / ${formatCount(stats.stalledCount)}`],
  ];
  const fragment = document.createDocumentFragment();
  rows.forEach(([name, value]) => {
    const dt = document.createElement("dt");
    dt.textContent = name;
    const dd = document.createElement("dd");
    dd.textContent = value;
    fragment.append(dt, dd);
  });
  latencyDebugListEl.replaceChildren(fragment);
}

async function renderLatencyStatus() {
  if (!latencyStatusEl) {
    return;
  }
  try {
    const response = await requestStatus();
    if (!response?.ok) {
      throw new Error(response?.error || "상태 확인 실패");
    }
    const latency = response.result?.lowLatency;
    if (!latency?.available) {
      latencyStatusEl.textContent = "라이브 탭에서만 사용 가능";
      renderLatencyDebug(null);
      return;
    }
    const modeLabel = {
      auto: "자동",
      fast: "빠른 반응",
      stable: "안정 우선",
      custom: "직접 설정",
    }[latency.mode] || "자동";
    const stateLabel = latency.userPaused ? "일시 중지" :
      latency.recovering ? "안정화 중" :
        latency.catchingUp ? "따라잡는 중" :
          latency.enabled ? "켜짐" : "꺼짐";
    latencyStatusEl.textContent = `${stateLabel} · ${modeLabel} · 플레이어 기준 ${formatSeconds(latency.latencySeconds)} 뒤 · 버퍼 ${formatSeconds(latency.bufferAheadSeconds)}`;
    renderLatencyDebug(latency);
  } catch (error) {
    latencyStatusEl.textContent = "라이브 탭 상태 확인 불가";
    renderLatencyDebug(null);
  }
}

document.querySelectorAll("[data-action]").forEach((button) => {
  button.addEventListener("click", async () => {
    try {
      const response = await sendAction(button.dataset.action);
      if (!response?.ok) {
        throw new Error(response?.error || "실행 실패");
      }
      await renderLatencyStatus();
      setStatus(button.dataset.action === "save-folder" && response.result?.canceled ? "폴더 선택 취소" : "완료");
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
    await renderLatencyStatus();
    setStatus("옵션 저장");
  });
});

document.getElementById("open-options").addEventListener("click", () => {
  chrome.runtime.openOptionsPage();
});

Promise.all([
  renderOptions(),
  renderLatencyStatus(),
]).catch((error) => setStatus(error.message || String(error)));
