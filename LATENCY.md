## 구현 반영 현황

현재 `extension/content.js`에는 다음 LAT 개선이 반영되어 있다.

```text
버전: 1.4.28
보정 중 반복 알림 제거
LAT 버튼 pointerdown 즉시 반응
확장 팝업에서 LAT 켜기/끄기 가능
확장 팝업에서 LAT 상태 표시
목표 딜레이/체크 간격 설정 지원
자동/빠른 반응/안정 우선/직접 설정 모드 지원
설정값 0초여도 내부 최소 0.75초 안전 목표 적용
버퍼 위험 시 15초 동안 최소 1.25초 목표로 백오프
suspend 이벤트를 버퍼 위험으로 보지 않음
seeking은 버퍼 위험이 아니라 이번 체크만 중단
사용자 seek 감지 시 LAT 10초 일시 중지
seekable은 edge 측정에 사용
실제 seek는 buffered 범위와 0.25초 가드를 확인한 뒤 실행
seek 조건은 기본 2회 연속 확인 후 실행
큰 밀림은 즉시 seek 가능
작은 밀림은 히스테리시스가 있는 배속 보정으로 처리
앞쪽 buffered 여유가 부족하면 보정을 멈추고 백오프
LAT 버튼 옆 설정 진입점 추가
확장 팝업 고급 상태 표시 추가
현재 탭 세션 기준 디버그 통계 수집 추가
반복 버퍼링 안정화 상태를 확장 아이콘 badge로 조용히 표시
확장 팝업은 모드 중심으로 정리하고 숫자 설정은 고급 영역으로 이동
LAT 제어 상태를 NORMAL/CATCH_UP/SEEKING/RECOVERY/PAUSED로 분리
seek 쿨다운은 seeked/playing 확인 시점에 갱신
waiting/stalled/playing/seeked/visibilitychange 발생 시 즉시 재검사
라이브 edge가 일정 시간 전진하지 않으면 자동 보정 중단
LAT 실행 실패 시 내부 오류명 대신 사용자 행동 지침 표시
LAT 버튼 표시 글자는 고정하고 상태는 색상/tooltip/badge로 표시
```

아직 남은 사용자 경험 개선:

```text
현재 문서 기준 필수 반영 항목 없음
```

## 사용자 관점 판정

현재 가장 큰 문제는 **기능이 아니라 설명과 상태 전달**입니다. 사용자는 `seekable`, 체크 간격, 안전 버퍼를 알고 싶어 하지 않습니다. 사용자가 궁금한 것은 세 가지입니다.

* LAT가 지금 실제로 작동하는가
* 버퍼링이 생기면 확장 프로그램이 무엇을 하는가
* 끄거나 되감았을 때 원래대로 돌아가는가

### 1. 설정 진입 경로부터 바꾸는 게 우선입니다

`chrome://extensions → 세부정보 → 옵션`은 일반 사용자가 다시 찾아가기 어렵습니다. LAT 버튼 옆 톱니바퀴나 확장 프로그램 팩업에서 바로 설정할 수 있어야 합니다. Chrome도 확장 프로그램의 action UI와 옵션 페이지를 사용자 기능 진입점으로 제공하므로, 고급 설정만 전체 옵션 페이지에 남기는 구성이 자연스럽습니다. ([Chrome for Developers][1])

권장 구조:

```text
LAT 버튼 클릭
-> 켜기/끄기

LAT 옆 ▼ 또는 확장 아이콘 클릭
-> 자동
-> 빠른 반응
-> 안정 우선
-> 고급 설정
```

`딜레이 체크 간격`은 일반 설정에서 숨기는 편이 낫습니다. 사용자가 잘못 낮춰도 체감 이득은 불명확하고, 설정 복잡도만 커집니다.

---

### 2. `목표 딜레이 0초` 표시는 바꿔야 합니다

사용자가 `0초`를 선택하면 실제 지연도 0초에 가깝다고 생각합니다. 그런데 실제 동작은 최소 0.75초이므로 현재 표시는 오해를 유발합니다.

다음 중 하나가 낫습니다.

```text
자동(권장)
빠른 반응
안정 우선
```

또는 고급 설정에서는:

```text
플레이어 기준 목표 거리: 0.75초
```

로 표시합니다.

`목표 딜레이`보다 아래 표현이 사용자에게 더 정확합니다.

```text
실시간에서 얼마나 뒤로 재생할지
```

설명 문구도 기술 용어를 줄여 다음 정도면 충분합니다.

```text
값이 낮을수록 실시간에 가깝지만,
네트워크 상태에 따라 끊김이 늘어날 수 있습니다.
```

---

### 3. 기본값은 숫자보다 `자동`이 낫습니다

처음 사용하는 사람은 자기 네트워크에 적합한 값을 모릅니다. 따라서 기본값을 `0초`나 `0.75초`로 제시하기보다 자동 모드가 더 적합합니다.

권장 모드:

```text
자동(기본)
버퍼 상태에 따라 약 0.75~1.5초 사이에서 자동 조정

빠른 반응
가능한 한 실시간에 가깝게 유지
끊김 가능성 증가

안정 우선
조금 더 여유를 두고 끊김을 줄임
```

실제 내부 숫자를 반드시 사용자에게 모두 보여줄 필요는 없습니다. 고급 설정에서만 확인하게 하면 됩니다.

기본 모드를 무조건 가장 공격적으로 설정하는 것은 권하지 않습니다. 첫 사용에서 버퍼링이 발생하면 사용자는 세부 설정을 조정하기보다 확장 프로그램 자체가 불안정하다고 판단할 가능성이 큽니다.

---

### 4. LAT 버튼 상태를 명확히 보여줘야 합니다

버튼이 단순히 `LAT`만 표시되면 다음 상태를 구분할 수 없습니다.

```text
기능 꺼짐
기능 켜짐
영상 탐색 중
배속으로 따라잡는 중
버퍼링 후 안정화 중
사용자 되감기로 일시 중지
라이브 영상이 아님
```

권장 상태 표시는 다음과 같습니다.

```text
LAT 꺼짐
LAT 켜짐
LAT 따라잡는 중
LAT 안정화 중
LAT 일시 중지
LAT 사용 불가
```

색상만으로 상태를 구분하지 말고 텍스트나 아이콘을 함께 사용해야 합니다. 버튼에는 `aria-pressed`, 키보드 포커스, 읽을 수 있는 이름도 넣는 편이 맞습니다. 접근성은 장애가 있는 사용자뿐 아니라 작은 화면, 느린 네트워크, 키보드 사용 등 다양한 상황의 사용자 경험에도 영향을 줍니다. ([W3C][2])

예:

```html
<button
  aria-pressed="true"
  aria-label="라이브 지연 줄이기 켜짐"
  title="라이브 지연 줄이기: 켜짐"
>
  LAT 켜짐
</button>
```

---

### 5. 화면 알림을 완전히 없애기보다 상태 변화만 알려야 합니다

보정할 때마다 알림을 띄우지 않는 현재 방향은 맞습니다. 배속이 1.01배로 바뀔 때마다 표시하면 방해가 됩니다.

다만 완전히 조용하면 사용자는 고장인지 정상 작동인지 알 수 없습니다. 다음 상황에서만 한 번 알려주는 것이 좋습니다.

```text
LAT를 켰을 때
LAT를 껐을 때
라이브 영상을 찾지 못했을 때
사용자가 되감아서 일시 중지됐을 때
반복 버퍼링으로 안정화 모드에 들어갔을 때
```

Chzzk 화면을 캡처하는 확장 프로그램이라면 영상 위 토스트가 녹화될 수 있으므로, 지속적인 오버레이보다 다음 방식이 낫습니다.

```text
LAT 버튼 문구 변경
버튼 tooltip
확장 프로그램 아이콘 badge
팝업 안 상태 표시
```

---

### 6. 사용자 일시정지와 되감기를 존중해야 합니다

이 부분은 사용자 신뢰에 직접 영향을 줍니다.

사용자가 잠시 멈췄는데 LAT가 자동으로 최신 위치로 점프하면 “기능이 내 조작을 무시한다”고 느낍니다. 사용자가 되감은 경우도 마찬가지입니다.

권장 동작:

```text
사용자 일시정지
-> LAT 보정도 일시정지
-> 재생 시 LAT 다시 시작

사용자 되감기
-> LAT 10초간 일시정지
또는
-> LAT 자동 해제
```

개인적으로는 되감기 시 자동 해제가 가장 예측 가능합니다.

표시:

```text
LAT 일시 중지 · 사용자가 재생 위치를 이동함
```

반대로 사용자가 직접 `LAT` 버튼을 다시 누르면 즉시 최신 위치로 복귀시키면 됩니다.

Chrome Web Store 품질 지침도 확장 프로그램이 사용자의 다른 설정과 선호를 존중해야 한다고 명시합니다. ([Chrome for Developers][3])

---

### 7. LAT를 끄면 반드시 완전히 원상복구해야 합니다

사용자가 LAT를 껐는데 `playbackRate`가 1.03이나 1.06으로 남아 있으면 치명적인 UX 결함입니다.

다음 상황 모두에서 원래 배속을 복구해야 합니다.

```text
LAT 버튼을 끔
영상 태그가 교체됨
페이지 이동
확장 프로그램 오류
라이브에서 VOD로 전환
사용자가 수동 탐색
기능이 적용 불가능한 상태
```

사용자 입장에서는 내부 예외가 발생했는지 알 수 없으므로, 실패 시에도 반드시 원상복구되는 구조가 필요합니다.

---

### 8. 현재 지연값은 보여주되, 과도하게 정확한 척하면 안 됩니다

현재 계산값은 서버부터 사용자 화면까지의 전체 지연이 아닙니다. 따라서 다음 표시는 좋지 않습니다.

```text
현재 지연: 0.83초
```

사용자는 이것을 실제 방송 송출 지연으로 받아들일 수 있습니다.

다음이 더 정확합니다.

```text
플레이어 기준: 약 0.8초 뒤
```

또는 일반 화면에서는 숫자를 감추고:

```text
상태: 실시간에 가까움
상태: 따라잡는 중
상태: 안정화 중
```

으로 표시할 수 있습니다.

고급 정보에서만 다음 값을 제공하면 충분합니다.

```text
플레이어 기준 거리: 약 0.9초
앞쪽 버퍼: 약 0.5초
적용 모드: 자동
현재 동작: 배속 보정
```

---

### 9. 실패를 조용히 무시하면 안 됩니다

다음 상황에 대한 사용자용 메시지가 필요합니다.

```text
라이브 영상이 아닙니다
재생을 시작한 뒤 다시 시도해 주세요
현재 플레이어에서는 LAT를 적용할 수 없습니다
영상이 교체되어 LAT를 다시 연결했습니다
반복 버퍼링으로 안정화 중입니다
```

버튼을 눌렀는데 아무 일도 일어나지 않는 경험이 가장 나쁩니다.

다만 메시지는 기술 오류가 아니라 행동 지침으로 써야 합니다.

나쁜 예:

```text
seekable range is empty
```

좋은 예:

```text
아직 재생 가능한 라이브 구간이 없습니다.
방송 재생 후 다시 시도해 주세요.
```

---

### 10. 설정 저장 범위를 명확히 해야 합니다

권장 기본 동작은 다음입니다.

```text
선택한 모드
-> 전체 Chzzk 방송에서 기억

LAT 켜짐/꺼짐
-> 현재 탭에서만 유지

방송 접속 시 자동 적용
-> 별도 옵션, 기본은 끔
```

LAT 활성화 상태를 모든 방송에 자동 적용하면 사용자가 VOD나 되감기를 이용할 때 예상치 못한 점프가 생길 수 있습니다.

설정 화면:

```text
[ ] 라이브 방송을 열면 LAT 자동 적용
```

---

## 추천 사용자 화면

```text
라이브 지연 줄이기                 [켜짐]

모드
● 자동(권장)
○ 빠른 반응
○ 안정 우선

현재 상태
실시간에 가까움
플레이어 기준 약 0.9초 뒤

[ ] 라이브 방송을 열면 자동 적용

고급 설정 >
```

고급 설정:

```text
플레이어 기준 목표 거리: 0.75초
상태 확인 간격: 0.75초

[기본값 복원]
```

`LAT`라는 약어는 유지해도 되지만, 최초 노출과 tooltip에는 반드시 `라이브 지연 줄이기`를 같이 써야 합니다.

## 사용자 관점 수정 우선순위

1. `목표 딜레이 0초`를 `자동`으로 변경
2. LAT 버튼에 현재 상태 표시
3. 설정 화면을 버튼이나 확장 팝업에서 바로 열 수 있게 변경
4. 사용자 일시정지·되감기 시 LAT가 조작을 양보하도록 변경
5. LAT 해제·오류·영상 교체 시 원래 배속 복구
6. 일반 설정은 모드 중심, 숫자 설정은 고급으로 이동
7. 실패 및 안정화 상태에 짧고 명확한 안내 추가

기술 로직과 사용자 경험을 합쳐 보면, **가장 먼저 고칠 것은 더 낮은 딜레이 값이 아니라 `자동 모드`, 명확한 상태 표시, 사용자 조작 존중입니다.**

[1]: https://developer.chrome.com/docs/extensions/develop/ui/options-page?utm_source=chatgpt.com "Give users options - Chrome for Developers"
[2]: https://www.w3.org/WAI/fundamentals/accessibility-intro/?utm_source=chatgpt.com "Introduction to Web Accessibility"
[3]: https://developer.chrome.com/docs/webstore/program-policies/quality-guidelines-faq?utm_source=chatgpt.com "Extensions quality guidelines FAQ - Program Policies"


## 판정

방향은 맞지만, 현재 로직은 **“0.75초를 안정적으로 유지하는 제어기”라기보다 “밀렸을 때만 앞으로 당기는 단방향 보정기”**에 가깝습니다. 지금도 동작은 하겠지만, 장시간 안정성을 믿기에는 아래 네 부분을 먼저 고치는 게 맞습니다.

### 1. `suspend`는 버퍼 위험 이벤트에서 빼는 게 맞습니다

`suspend`는 브라우저가 미디어 다운로드를 **의도적으로 중단하고 `NETWORK_IDLE`로 전환했다**는 뜻입니다. 버퍼가 충분하거나 지금 더 받을 필요가 없을 때도 발생할 수 있으므로, 이를 곧바로 15초 백오프로 연결하면 오탐 가능성이 큽니다. 반면 `waiting`은 재생할 데이터가 부족해 실제 재생이 멈춘 경우라 강한 신호입니다. ([html.spec.whatwg.org][1])

권장 분류는 다음과 같습니다.

```js
waiting  -> 강한 버퍼 위험
stalled  -> 약한 위험, buffered 상태와 함께 확인
suspend  -> 무시
seeking  -> 위험으로 표시하지 말고 이번 체크만 중단
```

특히 현재처럼:

```js
if (video.seeking) {
  markLowLatencyBufferRisk();
}
```

로 처리하면 **확장 프로그램이 직접 실행한 seek도 버퍼 위험으로 판정**합니다. 내부 seek 직후 스스로 백오프를 거는 구조가 되므로 다음처럼 분리해야 합니다.

```js
if (video.seeking) {
  return;
}
```

그리고 내부 seek에는 별도의 상태를 둡니다.

```js
lowLatencyInternalSeekInFlight = true;
```

`seeked` 또는 `playing` 이벤트에서 해제하는 방식이 안전합니다.

---

### 2. `seekable`은 딜레이 측정에 쓰고, 실제 seek 가능 여부는 `buffered`로 확인해야 합니다

현재 가장 위험한 부분입니다.

`seekable`은 “브라우저가 seek를 허용하는 범위”이지, 해당 지점의 데이터가 당장 버퍼에 있다는 뜻은 아닙니다. MSE에서는 플레이어가 설정한 live seekable range와 실제 buffered 범위를 합쳐 `seekable`을 만들 수도 있습니다. 따라서 `seekable.end() - target`으로 바로 이동하면 허용된 위치이기는 하지만 아직 데이터가 없는 위치일 수 있습니다. ([W3C][2])

구분은 이렇게 하는 게 맞습니다.

```text
seekable -> 라이브 edge 및 이동 허용 범위
buffered -> 실제로 현재 재생 가능한 데이터 범위
```

seek 대상은 다음 조건을 모두 만족해야 합니다.

```text
1. targetTime이 seekable 범위 안에 있음
2. targetTime이 buffered 범위 안에 있음
3. targetTime 이후로 최소 0.2~0.4초의 buffered 데이터가 있음
4. 현재 위치보다 충분히 앞임
```

개념적으로는 다음과 같습니다.

```js
const requestedTime = edge - targetLatency;
const safeTime = Math.min(
  requestedTime,
  liveBufferedRange.end - SEEK_BUFFER_GUARD_SECONDS
);
```

초기값은 다음 정도가 적당합니다.

```js
SEEK_BUFFER_GUARD_SECONDS = 0.25;
```

또한 무조건 마지막 `seekable` 범위를 사용하지 말고, 먼저 `currentTime`이 들어 있는 범위를 찾아야 합니다. 타임라인 단절이나 품질 전환으로 범위가 여러 개 생겼을 때 마지막 범위를 사용하면 예상치 못한 대형 점프가 발생할 수 있습니다.

```js
function findContainingRange(ranges, time, epsilon = 0.05) {
  for (let i = 0; i < ranges.length; i += 1) {
    const start = ranges.start(i);
    const end = ranges.end(i);

    if (time >= start - epsilon && time <= end + epsilon) {
      return { start, end };
    }
  }

  return null;
}
```

현재 위치가 어느 seekable 범위에도 포함되지 않으면 그 체크에서는 아무 행동도 하지 않는 편이 낫습니다.

---

### 3. 현재 배속 보정은 지나치게 느립니다

현재 식은 다음과 같습니다.

```js
deltaRate = overshoot * 0.015;
```

라이브 edge가 초당 1초씩 전진한다고 가정하면, 오차가 줄어드는 속도도 오차에 비례합니다.

예를 들어:

```text
오차 0.5초 -> 1.0075x
오차 1.0초 -> 1.015x
오차 1.3초 -> 1.0195x
```

오차가 `0.15초` 안정 마진 안으로 들어가는 데 걸리는 시간을 단순 계산하면 대략:

```text
0.5초 오차 -> 약 80초
1.0초 오차 -> 약 126초
1.3초 오차 -> 약 144초
```

즉, seek 기준인 `1.4초` 바로 아래에서는 2분 이상 천천히 따라잡을 수 있습니다. “딜레이 최소화” 목적에는 너무 느립니다.

오차를 일정 시간 안에 회복하도록 설계하는 편이 낫습니다.

```js
const error = latency - targetLatency;
const deltaRate = clamp(
  error / 25,
  0.01,
  0.06
);

video.playbackRate = baseRate + deltaRate;
```

이렇게 하면 대략 20~30초 내 회복을 목표로 하는 형태가 됩니다.

배속 변경에는 히스테리시스도 넣는 게 좋습니다.

```text
오차 0.30초 초과 -> 배속 보정 시작
오차 0.10초 미만 -> 배속 보정 종료
0.10~0.30초 -> 현재 상태 유지
```

예시:

```js
if (!lowLatencyRateCorrectionActive && error > 0.30) {
  lowLatencyRateCorrectionActive = true;
}

if (lowLatencyRateCorrectionActive && error < 0.10) {
  lowLatencyRateCorrectionActive = false;
}

if (lowLatencyRateCorrectionActive) {
  const deltaRate = clamp(error / 25, 0.01, 0.06);
  setPlaybackRate(baseRate + deltaRate);
} else {
  setPlaybackRate(baseRate);
}
```

`1.06x` 상한 자체는 당장 높일 필요 없습니다. 먼저 보정 곡선을 바꾸는 편이 낫습니다.

추가로 현재 식의:

```js
Math.min(0.08, ...)
```

은 기본 속도가 1배라면 최종 `1.06` clamp 때문에 일부가 의미 없습니다. 둘 중 하나만 남기는 게 명확합니다.

그리고 `baseRate > 1.06`이면 clamp의 최소값이 최대값보다 커질 수 있습니다. LAT가 활성화된 동안 기본 속도를 1배로 고정할지, 사용자 배속을 보존할지 명확히 결정해야 합니다.

---

### 4. 현재의 “최소 안전 목표 0.75초”는 실제 최소값이 아닙니다

현재 조건은:

```js
if (latency <= target + 0.15) {
  playbackRate = 1;
  return;
}
```

입니다.

따라서 현재 딜레이가 `0.3초`이고 목표가 `0.75초`여도 아무 행동을 하지 않습니다. 즉, 현재 로직은 딜레이를 0.75초까지 늘리지 않습니다.

따라서 정확한 의미는 다음입니다.

```text
0.75초보다 밀렸을 때 따라잡기 위한 보정 기준
```

이지:

```text
항상 최소 0.75초를 유지하는 목표
```

가 아닙니다.

두 가지 중 하나로 정리하는 게 좋습니다.

**딜레이 우선 모드**

```text
현재처럼 앞으로 당기기만 함
0.75초를 "보정 목표"라고 표기
뒤로 물리거나 1배 미만 배속은 사용하지 않음
```

**안정성 우선 모드**

```text
버퍼링 후 실제 목표보다 너무 가까우면 잠시 0.98x
목표 딜레이가 확보되면 1.00x
```

Shaka Player의 live-sync도 최대 배속뿐 아니라 최소 배속과 동적 목표 딜레이를 별도로 지원합니다. 즉, 백오프 목표를 실제로 확보하려면 느린 재생 방향도 필요합니다. ([shaka-player-demo.appspot.com][3])

개인적으로는 LAT의 기본 모드는 딜레이 우선으로 유지하고, 별도의 `자동 안정화` 옵션에서만 0.98x를 허용하는 편이 낫습니다.

---

## 추가로 바꿀 부분

### `readyState` 대신 실제 앞쪽 버퍼 시간을 같이 봐야 합니다

`HAVE_FUTURE_DATA`는 “적어도 조금 더 재생할 데이터가 있다”는 뜻이며, 극단적으로 현재 프레임과 다음 프레임 정도일 수도 있습니다. 몇 초의 버퍼가 있다는 의미는 아닙니다. ([html.spec.whatwg.org][1])

따라서 다음 값을 계산하는 게 좋습니다.

```js
function bufferAheadSeconds(video) {
  const currentTime = video.currentTime;
  const ranges = video.buffered;

  for (let i = 0; i < ranges.length; i += 1) {
    const start = ranges.start(i);
    const end = ranges.end(i);

    if (currentTime >= start - 0.05 && currentTime <= end + 0.05) {
      return Math.max(0, end - currentTime);
    }
  }

  return 0;
}
```

초기 판단값은 다음 정도로 시작할 수 있습니다.

```text
bufferAhead < 0.20초 -> 강한 위험
bufferAhead < 0.50초 -> 배속 보정 금지
bufferAhead >= 0.50초 -> 일반 보정 가능
```

이는 고정 정답이 아니라 CHZZK 재생 데이터를 보고 조정해야 하는 값입니다.

---

### 백오프는 단일 타임스탬프보다 상태로 관리하는 편이 낫습니다

최소한 다음 네 상태가 있으면 로직이 훨씬 명확해집니다.

```text
NORMAL
CATCH_UP
SEEKING
RECOVERY
```

`RECOVERY` 진입 조건:

```text
waiting 발생
짧은 시간 내 stalled 반복
bufferAhead가 매우 낮음
seek 직후 waiting 발생
```

복귀 조건:

```text
playing 상태가 일정 시간 유지
bufferAhead가 회복됨
추가 waiting이 없음
```

또한 seek 쿨다운은 `currentTime`을 설정한 시점이 아니라 `seeked` 또는 `playing`이 발생한 시점부터 시작하는 게 맞습니다. seek에 2초가 걸리면 현재 방식의 6초 쿨다운은 실제로 4초만 남기 때문입니다.

---

### seek는 한 번의 측정만으로 실행하지 않는 게 좋습니다

`seekable.end()`는 세그먼트나 파트가 추가될 때 계단식으로 증가할 수 있습니다. 그때 계산 딜레이도 순간적으로 튑니다.

따라서:

```text
배속 시작 -> 조건 2회 연속 확인
일반 seek -> 조건 2회 연속 확인
매우 큰 밀림 -> 즉시 seek
```

정도로 나누는 게 좋습니다.

예시:

```text
오차 1.4초 이상 2회 연속 -> seek
오차 3초 이상 -> 즉시 seek
```

edge가 갑자기 뒤로 이동하거나 예상보다 크게 점프하면 품질 전환이나 타임라인 변경일 수 있으므로 컨트롤러 상태를 초기화해야 합니다.

---

### 일시정지와 사용자 seek 처리를 정해야 합니다

다음 조건에서는 절대로 자동 seek나 배속을 수행하지 않는 게 안전합니다.

```js
if (video.paused || video.ended) {
  restoreBasePlaybackRate();
  return;
}
```

사용자가 직접 뒤로 돌린 경우도 현재 LAT가 바로 앞으로 다시 끌고 갈 수 있습니다. 사용자 seek를 감지하면 다음 중 하나가 낫습니다.

```text
LAT 자동 해제
LAT 10초간 일시중지
"수동 탐색 중" 상태로 전환
```

내부 seek와 사용자 seek는 반드시 구분해야 합니다.

---

### 라이브 영상인지 검증해야 합니다

VOD도 `seekable` 범위를 가지므로 video 태그만 보고 적용하면 영상 끝으로 당길 수 있습니다.

사이트의 라이브 상태를 직접 확인할 수 없다면 다음처럼 edge가 실제로 전진하는지 확인할 수 있습니다.

```text
3회 이상 측정
seekable edge가 경과 시간에 따라 계속 전진
고정된 edge라면 LAT 중단
```

`duration === Infinity`만으로 판정하는 것은 충분하지 않습니다. MSE의 seekable은 duration이나 플레이어가 설정한 live seekable range에 따라 구성될 수 있습니다. ([W3C][2])

---

### 0.25초 폴링은 보조 수단으로 두는 게 낫습니다

Chrome은 숨겨진 페이지에서 연쇄 `setTimeout`과 `setInterval`을 제한할 수 있으므로 250ms 간격이 항상 보장되지는 않습니다. 이벤트 기반 확인과 저빈도 폴링을 함께 쓰는 편이 안정적입니다. ([Chrome for Developers][4])

권장 구성:

```text
기본 폴링: 0.5~1초
waiting, stalled, playing, seeked 발생 시 즉시 재검사
visibilitychange 후 즉시 재검사
0.25초는 고급 설정으로만 제공
```

---

## 설정 화면도 바꾸는 편이 낫습니다

현재 `목표 딜레이 0초`는 실제 동작과 다릅니다.

다음 중 하나가 명확합니다.

```text
자동(공격적) -> 실제 보정 기준 최소 0.75초
직접 설정 -> 0.75~5초
```

또는 이름을 다음처럼 바꿉니다.

```text
플레이어 edge 기준 보정 목표
```

현재 지연이 서버부터 화면까지의 전체 딜레이가 아니라는 점도 설정 화면에 짧게 표시하는 편이 좋습니다.

고급 상태 표시에는 다음 네 값이면 충분합니다.

```text
현재 edge 거리
앞쪽 buffered 시간
현재 적용 목표
현재 상태: 정상 / 배속 / seek / 복구
```

---

## 수정 우선순위

가장 먼저 할 작업은 이 순서가 좋습니다.

1. `suspend` 위험 판정 제거, `seeking`은 단순 return 처리
2. 내부 seek와 사용자 seek 구분
3. seek 시 `buffered` 범위와 0.25초 가드 확인
4. 배속 식을 `error / 20~30초` 형태로 변경하고 히스테리시스 추가
5. pause·VOD·다중 seekable range 방어
6. 디버그 통계 추가 후 0.75·1.25·1.4·15초 값 재조정

`0.75초`를 더 낮추거나 최대 배속을 더 높이는 것은 지금 단계에서는 권하지 않습니다. hls.js도 라이브 목표가 지나치게 낮으면 stall 가능성이 커진다고 명시하며, 가능한 경우 manifest의 part/hold-back 또는 세그먼트 특성에서 목표를 정합니다. 따라서 `0.75초`는 “안전 상수”가 아니라 CHZZK 환경에서 검증해야 할 튜닝값으로 보는 게 정확합니다. ([GitHub][5])

[1]: https://html.spec.whatwg.org/multipage/media.html "HTML Standard"
[2]: https://www.w3.org/TR/media-source-2/ "Media Source Extensions™"
[3]: https://shaka-player-demo.appspot.com/docs/api/shaka.extern.html "JSDoc: Class: shaka.extern"
[4]: https://developer.chrome.com/blog/timer-throttling-in-chrome-88 "Heavy throttling of chained JS timers beginning in Chrome 88  |  Blog  |  Chrome for Developers"
[5]: https://github.com/video-dev/hls.js/blob/master/docs/API.md "hls.js/docs/API.md at master · video-dev/hls.js · GitHub"
