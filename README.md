# RegionCapture

Windows용 영역 캡쳐 도구입니다. 원하는 화면 구역을 마우스로 드래그해 저장하고, 저장된 영역을 버튼이나 전역 단축키로 다시 캡쳐할 수 있습니다.

## 주요 기능

- 마우스 드래그로 캡쳐 영역 선택
- 저장된 영역을 즉시 다시 캡쳐
- 초 단위 자동 반복 캡쳐
- 저장 폴더 선택 및 설정 유지
- 전역 단축키 설정
- 키보드 직접 입력 방식의 단축키 등록
- NumPad 키 지원
- 캡쳐/단축키/오류 로그 분리 저장

## 다운로드와 실행

1. 이 저장소에서 `RegionCapture.exe`를 내려받습니다.
2. 원하는 폴더에 넣고 더블클릭합니다.
3. Windows 보안 경고가 뜨면 게시자를 확인한 뒤 실행 여부를 선택합니다.

Python 설치는 필요 없습니다. `RegionCapture.exe` 안에 필요한 실행 환경이 포함되어 있습니다.

## 사용 방법

1. `폴더 선택`으로 캡쳐 저장 위치를 고릅니다.
2. `영역 선택 후 캡쳐`를 누릅니다.
3. 화면이 어두워지면 저장할 구역을 드래그합니다.
4. 같은 영역은 `저장된 영역 바로 캡쳐`로 다시 캡쳐합니다.
5. 반복 저장이 필요하면 `자동 캡쳐 간격`에 초를 입력하고 `자동 시작`을 누릅니다.

## 단축키

기본 단축키는 다음과 같습니다.

- 영역 선택 후 캡쳐: `Ctrl + Alt + S`
- 저장된 영역 바로 캡쳐: `Ctrl + Alt + C`
- 자동 캡쳐 시작/중지: `Ctrl + Alt + A`

단축키를 바꾸려면 `키 입력` 버튼을 누른 뒤 원하는 키 조합을 실제로 누르세요. 직접 `+` 문자를 입력할 필요가 없습니다.

예시:

- `Ctrl+Alt+S`
- `Ctrl+Shift+F9`
- `Num0`
- `Num1`
- `NumDecimal`

NumPad 키를 사용할 수 있습니다. 일부 환경에서는 `Alt+NumPad` 조합이 Windows의 문자 입력 기능과 겹칠 수 있으므로, 키패드만 쓰거나 `Ctrl`, `Shift` 조합을 권장합니다.

## 설정 저장

처음 실행하면 프로그램 폴더에 `config.json`이 생성됩니다. 프로그램을 껐다 켜도 아래 설정이 유지됩니다.

- 저장 폴더
- 파일명 접두어
- 이미지 형식
- 마지막 캡쳐 영역
- 자동 캡쳐 간격
- 전역 단축키

기본 설정 예시는 `config.example.json`에서 확인할 수 있습니다.

## 로그

문제가 생기면 프로그램 폴더의 로그를 확인하세요.

- `region_capture_key_input.log`: 단축키 입력창에서 받은 키 값
- `region_capture_hotkey_process.log`: 단축키 적용, 등록, 보조 감지 시작 과정
- `region_capture_hotkey_event.log`: 단축키 수신과 실행 이벤트
- `region_capture_error.log`: 오류와 예외

## 문제 해결

단축키가 안 먹는 경우:

- 같은 단축키를 다른 프로그램이 쓰고 있는지 확인하세요.
- 프로그램 화면에서 `전역 단축키 사용`이 켜져 있는지 확인하세요.
- 관리자 권한 프로그램이나 게임 위에서 동작하지 않으면 `RegionCapture.exe`도 관리자 권한으로 실행해 보세요.
- NumPad 키가 원하는 값으로 저장되는지 `region_capture_key_input.log`를 확인하세요.

캡쳐가 안 되는 경우:

- 저장 폴더 권한을 확인하세요.
- `Program Files` 같은 보호 폴더보다 사용자 폴더에서 실행하는 것을 권장합니다.
- Windows 보안 정책이나 일부 DRM/게임 화면은 캡쳐가 제한될 수 있습니다.

## 개발용 실행

소스에서 직접 실행하려면 Windows에서 Python 3.11 이상을 설치한 뒤 아래 명령을 사용합니다.

```powershell
python -m venv .venv
.venv\Scripts\pip install -r requirements.txt
.venv\Scripts\python region_capture.py
```

실행 파일 빌드:

```powershell
.venv\Scripts\python -m PyInstaller --noconfirm --onefile --windowed --name RegionCapture --distpath . --workpath build --specpath build region_capture.py
```
