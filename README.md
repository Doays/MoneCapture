# Chzzk capture

CHZZK 라이브/비디오 페이지에서 동작하는 Chromium 확장 프로그램입니다.

Chrome, Naver Whale, Edge 같은 Manifest V3 지원 브라우저에서 사용할 수 있습니다.

## 기능

- 현재 영상 프레임 스크린샷
- 0.01~5초 이전 프레임 캡쳐
- SHOT/BACK 단축키 연속 캡쳐
- 영상 녹화
- 녹화 최대 5분 제한
- 방송 세션별 날짜/제목 폴더 저장
- 같은 방송 제목 변경/자정 넘김에도 같은 폴더 유지
- 다음 방송은 새 폴더로 분리
- 5초 탐색
- 화면 버튼 숨김/표시

## 설치 방법

1. 브라우저에서 `chrome://extensions`를 엽니다.
2. 오른쪽 위 `개발자 모드`를 켭니다.
3. `압축해제된 확장 프로그램을 로드`를 누릅니다.
4. 이 저장소 안의 `extension` 폴더를 선택합니다.
5. CHZZK 라이브 또는 비디오 페이지를 새로고침합니다.

## 사용 방법

CHZZK 페이지에서 영상 정보 오른쪽에 버튼이 표시됩니다.

- `SHOT`: 현재 영상 프레임 캡쳐
- `BACK`: 설정한 시간만큼 이전 프레임 캡쳐
- `REC`: 녹화 시작/중지
- `LAT`: 라이브 딜레이 감시
- 눈 모양 버튼: 화면 버튼 숨김

팝업에서 `설정 열기`를 누르면 기능 표시 여부, 단축키, BACK 캐시, 녹화 프리셋, 저장 폴더를 설정할 수 있습니다.

## 저장 방식

기본값은 폴더 직접 저장입니다.

처음 저장할 때 폴더를 선택하면, 선택한 폴더 아래에 방송 날짜와 제목으로 된 하위 폴더가 만들어지고 그 안에 스크린샷과 녹화 파일이 저장됩니다.

같은 방송에서는 제목이 바뀌거나 자정이 지나도 같은 폴더를 유지합니다. 다음 방송은 CHZZK 방송 세션 정보를 기준으로 새 폴더로 분리합니다.

## 녹화 제한

녹화는 정책 제한으로 5분까지만 저장됩니다.

5분에 도달하면 자동으로 녹화를 멈추고 파일을 저장합니다.

## 검증

Windows 프로젝트 루트에서 실행합니다.

```powershell
.venv\Scripts\python - <<'PY'
import json
from pathlib import Path

root = Path("extension")
manifest = json.loads((root / "manifest.json").read_text(encoding="utf-8"))
assert manifest["manifest_version"] == 3
assert manifest["name"] == "Chzzk capture"
assert (root / "content.js").exists()
assert (root / "shared.js").exists()
assert (root / "icons/icon128.png").exists()

content = (root / "content.js").read_text(encoding="utf-8")
assert "RECORD_MAX_DURATION_MS" in content

print(manifest["name"], manifest["version"])
PY
```
