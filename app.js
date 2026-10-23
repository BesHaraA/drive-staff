'use strict';
/*
 * ドライブスタフ 段階1
 *  - 行程（地点・予定時刻）を端末内に保存し、GPS で遅れ・早着を判定する
 *  - 到着・出発は自動判定（半径100m以内で1分停車＝到着／範囲外へ走り出す＝出発）。停車中は手でも押せる
 *  - ナビは Google マップアプリへ受け渡す
 *  - ?sim=1 を付けると、GPS の代わりに行程どおり走るシミュレーションで動く（PC での確認用）
 */

// ---- 判定の基準（要件定義 Q4・Q8・Q13） ----
const ROUTE_FACTOR = 1.3;     // 直線距離 → 道のりの概算係数
const DEFAULT_KMH = 40;       // 走行速度の実績がまだ無いときの平均速度
const ARRIVE_R = 100;         // 自動の到着判定の半径（m）
const NEAR_R = 200;           // 「到着」ボタンを大きく出す半径（m）
const ARRIVE_STOP_MS = 60e3;  // 自動の到着判定に必要な停車時間
const MOVING_MS = 2.0;        // この速さ（m/秒 ≒ 7km/h）を超えたら走行中とみなす
const ONTIME_MIN = 5;         // ±5分以内は定時

const LS_TRIP = 'ds.trip', LS_DIAG = 'ds.diag', LS_LAYOUT = 'ds.layout';
const SIM = new URLSearchParams(location.search).has('sim');
const $ = (id) => document.getElementById(id);

// ---- 保存（端末内）。読めない環境でも動くよう try で包む ----
const store = {
  get(k, d) { try { const v = localStorage.getItem(k); return v ? JSON.parse(v) : d; } catch (e) { return d; } },
  set(k, v) { try { localStorage.setItem(k, JSON.stringify(v)); } catch (e) { /* 保存できなくても画面は動かす */ } },
};

// ---- 時刻 ----
let simT = null, simX = 60, simPaused = false, simJamUntil = 0;
const now = () => (SIM ? simT : Date.now());
const pad = (n) => String(n).padStart(2, '0');
const fmt = (ts) => { if (ts == null) return '—'; const d = new Date(ts); return `${d.getHours()}:${pad(d.getMinutes())}`; };
const mins = (ms) => Math.round(ms / 60000);
function hhmmToTs(date, hhmm) {
  if (!hhmm) return null;
  const [h, m] = hhmm.split(':').map(Number);
  const d = new Date(`${date}T00:00:00`);
  d.setHours(h, m, 0, 0);
  return d.getTime();
}
const today = () => { const d = new Date(); return `${d.getFullYear()}-${pad(d.getMonth() + 1)}-${pad(d.getDate())}`; };

// ---- 距離 ----
function distM(a, b) {
  const R = 6371e3, rad = Math.PI / 180;
  const dLat = (b.lat - a.lat) * rad, dLng = (b.lng - a.lng) * rad;
  const s = Math.sin(dLat / 2) ** 2 + Math.cos(a.lat * rad) * Math.cos(b.lat * rad) * Math.sin(dLng / 2) ** 2;
  return 2 * R * Math.asin(Math.sqrt(s));
}

// ---- 行程 ----
// サンプルは公共の場所のみ（自宅などは入れない）。時刻は「今から15分後に出発」に合わせる
// （シミュレーションでは 8:00 発に固定して、確認のたびに同じ動きになるようにする）
function sampleTrip() {
  const d = new Date();
  let start = SIM ? 8 * 60 : d.getHours() * 60 + d.getMinutes() + 15;
  start = Math.ceil(start / 5) * 5;
  if (start + 170 >= 24 * 60) start = 8 * 60; // 日をまたぐ場合は翌日扱いにせず 8:00 発にする
  const t = (m) => `${pad(Math.floor((start + m) / 60))}:${pad((start + m) % 60)}`;
  return {
    title: '東京駅 → 箱根湯本（サンプル）', date: today(),
    points: [
      { name: '東京駅', lat: 35.6812, lng: 139.7671, arr: '', dep: t(0) },
      { name: '海老名SA（下り）', lat: 35.4489, lng: 139.3929, arr: t(50), dep: t(70) },
      { name: '小田原城', lat: 35.2509, lng: 139.1535, arr: t(110), dep: t(150) },
      { name: '箱根湯本駅', lat: 35.2325, lng: 139.1053, arr: t(170), dep: '' },
    ],
    log: {},
  };
}
let trip = store.get(LS_TRIP, null) || sampleTrip();
const P = () => trip.points;
const last = () => P().length - 1;
const plannedArr = (i) => hhmmToTs(trip.date, P()[i].arr);
const plannedDep = (i) => hhmmToTs(trip.date, P()[i].dep);
const logOf = (i) => (trip.log[i] = trip.log[i] || {});
const saveTrip = () => store.set(LS_TRIP, trip);

// 今どの地点を扱っているか：before＝出発前／enroute＝向かっている／at＝停車中／finished＝到着済み
function current() {
  for (let i = 0; i <= last(); i++) {
    const l = trip.log[i] || {};
    if (i === last()) return l.arr ? { i, mode: 'finished' } : { i, mode: i === 0 ? 'before' : 'enroute' };
    if (!l.dep) return { i, mode: i === 0 ? 'before' : (l.arr ? 'at' : 'enroute') };
  }
  return { i: last(), mode: 'finished' };
}

// ---- GPS と走行状態 ----
let pos = null, prevPos = null, moving = false, speedKmh = null, nearStopSince = null, nearEnter = null;
const gps = { fixes: 0, lastGapS: null, maxGapS: 0, acc: null, err: null };

function onPosition(p) {
  // p = { lat, lng, acc, spd(m/秒 または null), ts }
  if (pos) {
    const gap = (p.ts - pos.ts) / 1000;
    gps.lastGapS = gap; if (gap > gps.maxGapS) gps.maxGapS = gap;
    if (!SIM && gap > 30) diag(`GPS の更新が ${Math.round(gap)} 秒途切れた`);
    // 端末が速度を返さないときは移動距離から求める。ただし移動が位置の誤差の範囲内なら止まっているとみなす（GPS の揺れ対策）
    if (p.spd == null && gap > 0) {
      const moved = distM(pos, p), noise = Math.max(20, (p.acc || 0) + (pos.acc || 0));
      p.spd = moved > noise ? moved / gap : 0;
    }
  }
  prevPos = pos; pos = p;
  gps.fixes++; gps.acc = p.acc; gps.err = null;
  const wasMoving = moving;
  // 精度が粗い（±50m超）ときに端末が返す速度は当てにならないので、走行の判定に使わない
  moving = (p.spd || 0) > MOVING_MS && (SIM || (p.acc || 0) <= 50);
  if (moving) { const k = p.spd * 3.6; speedKmh = speedKmh == null ? k : speedKmh * 0.9 + k * 0.1; }
  if (wasMoving !== moving) diag(moving ? '走行開始' : '停車');
  autoJudge();
  render();
}

// 到着・出発の自動判定（要件 F10）
function autoJudge() {
  if (!pos) return;
  const c = current(); if (c.mode === 'finished') return;
  const d = distM(pos, P()[c.i]);
  if (c.mode === 'before' || c.mode === 'at') {
    if (moving && d > ARRIVE_R) record(c.i, 'dep', pos.ts, true);
  } else if (c.mode === 'enroute') {
    if (d <= ARRIVE_R) { if (nearEnter == null) nearEnter = pos.ts; }
    if (d <= ARRIVE_R && !moving) {
      if (nearStopSince == null) nearStopSince = pos.ts;
      if (pos.ts - nearStopSince >= ARRIVE_STOP_MS) record(c.i, 'arr', nearStopSince, true);
    } else nearStopSince = null;
    // 止まらずに通り過ぎた：範囲に入った時刻を到着、出た時刻を出発として記録する
    if (nearEnter != null && d > ARRIVE_R * 1.5 && moving && c.i < last()) {
      const enter = nearEnter;
      record(c.i, 'arr', enter, true); record(c.i, 'dep', pos.ts, true);
      diag(`${P()[c.i].name} は通過扱い`);
    }
  }
}
function record(i, kind, ts, auto) {
  logOf(i)[kind] = ts; logOf(i)[kind + 'Auto'] = auto;
  nearStopSince = null; nearEnter = null;
  saveTrip();
  diag(`${P()[i].name} ${kind === 'arr' ? '到着' : '出発'} ${fmt(ts)}（${auto ? '自動' : '手動'}）`);
}

// ---- 見込み時刻の計算 ----
function legMs(j) { // 地点 j-1 → j の予定所要時間
  const a = plannedDep(j - 1), b = plannedArr(j);
  if (a != null && b != null && b > a) return b - a;
  return distM(P()[j - 1], P()[j]) * ROUTE_FACTOR / (DEFAULT_KMH / 3.6) * 1000;
}
const stayMs = (i) => { const a = plannedArr(i), b = plannedDep(i); return a != null && b != null && b > a ? b - a : 0; };
function estimate() {
  const t = now(), c = current(), est = [];
  for (let i = 0; i <= last(); i++) {
    const l = trip.log[i] || {}, e = { arr: null, dep: null, actual: false };
    if (i < c.i || c.mode === 'finished') {
      e.arr = l.arr ?? null; e.dep = l.dep ?? null; e.actual = true;
    } else if (i === c.i) {
      if (c.mode === 'before') e.dep = Math.max(plannedDep(0) ?? t, t);
      else if (c.mode === 'at') { e.arr = l.arr; e.dep = Math.max(plannedDep(i) ?? 0, l.arr + stayMs(i), t); }
      else { // enroute
        const kmh = speedKmh ?? DEFAULT_KMH;
        const remain = pos ? distM(pos, P()[i]) * ROUTE_FACTOR : null;
        e.arr = remain != null ? t + remain / (kmh / 3.6) * 1000 : (est[i - 1].dep ?? t) + legMs(i);
        if (i < last()) e.dep = Math.max(plannedDep(i) ?? 0, e.arr + stayMs(i));
      }
    } else {
      e.arr = (est[i - 1].dep ?? t) + legMs(i);
      if (i < last()) e.dep = Math.max(plannedDep(i) ?? 0, e.arr + stayMs(i));
    }
    est.push(e);
  }
  return est;
}
function diffSpan(ms) {
  if (ms == null) return '';
  const m = mins(ms);
  if (Math.abs(m) <= ONTIME_MIN) return `<span class="c-ok">${m === 0 ? '±0' : (m > 0 ? '+' : '') + m + '分'}</span>`;
  return m > 0 ? `<span class="c-late">+${m}分</span>` : `<span class="c-early">${m}分</span>`;
}

// ---- 描画 ----
function render() {
  const t = now(), c = current(), est = estimate(), cp = P()[c.i];
  $('clock').textContent = fmt(t);
  $('tripTitle').textContent = trip.title;
  const g = $('gpsState');
  if (SIM) { g.textContent = 'GPS（模擬）'; g.className = 'gps ok'; }
  else if (gps.err) { g.textContent = 'GPS ×'; g.className = 'gps ng'; }
  else if (pos) { g.textContent = `GPS ±${Math.round(gps.acc)}m`; g.className = 'gps ok'; }

  // 状態の帯
  let cls = '', big = '', sub = '';
  if (c.mode === 'finished') {
    const m = mins(trip.log[last()].arr - plannedArr(last()));
    cls = Math.abs(m) <= ONTIME_MIN ? 'ok' : (m > 0 ? 'late' : 'early'); big = '到着';
    sub = `${fmt(trip.log[last()].arr)} 着（予定 ${fmt(plannedArr(last()))}）`;
  } else if (c.mode === 'before') {
    const dep = plannedDep(0), late = dep != null ? mins(t - dep) : 0;
    if (late > ONTIME_MIN) { cls = 'late'; big = `${late}分遅れ`; sub = `出発予定 ${fmt(dep)} を過ぎています`; }
    else { cls = ''; big = '出発前'; sub = dep != null ? `${fmt(dep)} 発 まで あと ${Math.max(0, -late)}分` : ''; }
  } else if (c.mode === 'at') {
    const m = mins(est[c.i].dep - (plannedDep(c.i) ?? est[c.i].dep));
    cls = Math.abs(m) <= ONTIME_MIN ? '' : (m > 0 ? 'late' : '');
    big = m > ONTIME_MIN ? `${m}分遅れ` : '停車中';
    sub = `${cp.name} ${fmt(trip.log[c.i].arr)} 着<br>出発予定 ${fmt(plannedDep(c.i))}（あと ${Math.max(0, mins((plannedDep(c.i) ?? t) - t))}分）`;
  } else {
    const m = mins(est[c.i].arr - (plannedArr(c.i) ?? est[c.i].arr));
    if (Math.abs(m) <= ONTIME_MIN) { cls = 'ok'; big = '定時'; }
    else if (m > 0) { cls = 'late'; big = `${m}分遅れ`; }
    else { cls = 'early'; big = `${-m}分早い`; }
    const dk = pos ? distM(pos, cp) : null; // 高さが足りないと「次の地点」欄を隠すので、帯にも距離を出す
    const dTxt = dk == null ? '' : (dk < 1000 ? `（あと ${Math.round(dk)} m）` : `（あと ${(dk * ROUTE_FACTOR / 1000).toFixed(1)} km）`);
    sub = `次：${cp.name}${dTxt}<br>見込み ${fmt(est[c.i].arr)} 着（予定 ${fmt(plannedArr(c.i))}）`;
  }
  $('status').className = 'status ' + cls;
  $('status').innerHTML = `<span class="big">${big}</span><span class="sub">${sub}</span>`;

  // 次の地点カード
  const target = c.mode === 'before' || c.mode === 'at' ? P()[Math.min(c.i + 1, last())] : cp;
  const ti = c.mode === 'before' || c.mode === 'at' ? Math.min(c.i + 1, last()) : c.i;
  $('nextName').textContent = c.mode === 'finished' ? '—' : target.name;
  const dNext = pos ? distM(pos, target) : null;
  $('nextDist').textContent = dNext == null ? '— km' : (dNext < 1000 ? `あと ${Math.round(dNext)} m` : `あと ${(dNext * ROUTE_FACTOR / 1000).toFixed(1)} km`);
  $('nextEta').textContent = c.mode === 'finished' ? '' : `見込み ${fmt(est[ti].arr)} 着`;
  $('navBtn').disabled = c.mode === 'finished';

  // スタフ表（走行中は「記録」列を出さない。操作は下の常設バーで行う）
  $('staffTable').innerHTML = '<tr><th>地点</th><th>予定 着/発</th><th>見込み</th><th>差</th></tr>' + P().map((p, i) => {
    const e = est[i], kind = i === 0 ? '出発地' : (i === last() ? '到着地' : (stayMs(i) ? `立寄 ${mins(stayMs(i))}分` : '経由'));
    const rowCls = e.actual ? 'done' : (i === c.i ? 'cur' : '');
    const both = e.actual || (i === c.i && c.mode === 'at'); // 済んだ地点と停車中の地点は「着 / 発」を並べる
    const estTxt = both ? `${e.arr ? fmt(e.arr) : ''}${e.arr && e.dep ? ' / ' : ''}${e.dep ? fmt(e.dep) : ''}` : fmt(i === 0 ? e.dep : e.arr);
    const diff = e.actual ? '<span class="c-ok">実績</span>' : (i === 0 ? diffSpan(e.dep - plannedDep(0)) : diffSpan(plannedArr(i) != null ? e.arr - plannedArr(i) : null));
    return `<tr class="${rowCls}"><td class="nm">${i === c.i && !e.actual ? '▶ ' : ''}${esc(p.name)}<span class="k">${kind}</span></td>` +
      `<td class="t">${p.arr ? hm(p.arr) : '　'} / ${p.dep ? hm(p.dep) : '　'}</td><td class="t">${estTxt}</td><td>${diff}</td></tr>`;
  }).join('');

  // 常設の操作バー（要件 F10・Q13）
  const arrBtn = $('btnArr'), depBtn = $('btnDep');
  const dCur = pos && c.mode === 'enroute' ? distM(pos, cp) : null;
  const near = dCur != null && dCur <= NEAR_R;
  arrBtn.className = 'a2' + (near ? ' big' : '');
  arrBtn.textContent = near ? `${cp.name}に到着` : '到着';
  arrBtn.disabled = moving || c.mode !== 'enroute';
  depBtn.className = 'a2' + (c.mode === 'at' && !moving ? ' go' : '');
  depBtn.textContent = (c.mode === 'at' || c.mode === 'before') && !moving ? `${cp.name}を出発` : '出発';
  depBtn.disabled = moving || !(c.mode === 'before' || c.mode === 'at');
  $('lockNote').hidden = !moving;

  if ($('viewDiag').classList.contains('on')) renderDiag();
}
const hm = (s) => s.replace(/^0/, '');
const esc = (s) => String(s).replace(/[&<>"']/g, (ch) => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[ch]));

// ---- ボタン ----
$('btnArr').onclick = () => { const c = current(); if (!moving && c.mode === 'enroute') { record(c.i, 'arr', now(), false); render(); } };
$('btnDep').onclick = () => { const c = current(); if (!moving && (c.mode === 'before' || c.mode === 'at')) { record(c.i, 'dep', now(), false); render(); } };

// ナビ：次の地点を Google マップアプリで開く。iPhone はアプリの専用リンクを先に試す
$('navBtn').onclick = () => {
  const c = current(); if (c.mode === 'finished') return;
  const ti = c.mode === 'before' || c.mode === 'at' ? Math.min(c.i + 1, last()) : c.i;
  const p = P()[ti];
  const web = `https://www.google.com/maps/dir/?api=1&destination=${p.lat},${p.lng}&travelmode=driving&dir_action=navigate`;
  const ios = /iPhone|iPad|iPod/.test(navigator.userAgent);
  diag(`ナビ開始：${p.name}（${ios ? 'iOS アプリ用リンク' : 'Web リンク'}）`);
  if (SIM) { diag('（シミュレーション中のためナビは開かない）'); return; }
  if (ios) {
    location.href = `comgooglemaps://?daddr=${p.lat},${p.lng}&directionsmode=driving`;
    setTimeout(() => { if (document.visibilityState === 'visible') location.href = web; }, 1500);
  } else location.href = web;
};

// 画面の切替
document.querySelectorAll('.foot button[data-v]').forEach((b) => b.onclick = () => {
  document.querySelectorAll('.foot button[data-v]').forEach((x) => x.classList.toggle('on', x === b));
  document.querySelectorAll('.view').forEach((v) => v.classList.toggle('on', v.id === b.dataset.v));
  if (b.dataset.v === 'viewPlan') renderPlan();
  render();
});
// 縦横の切替：自動 → 横固定 → 縦固定（要件 Q6）
let layout = store.get(LS_LAYOUT, 'auto');
function applyLayout() {
  document.body.classList.toggle('force-land', layout === 'land');
  document.body.classList.toggle('force-port', layout === 'port');
  $('layoutBtn').textContent = { auto: '縦横:自動', land: '縦横:横', port: '縦横:縦' }[layout];
}
$('layoutBtn').onclick = () => { layout = { auto: 'land', land: 'port', port: 'auto' }[layout]; store.set(LS_LAYOUT, layout); applyLayout(); };
applyLayout();

// ---- 計画画面 ----
let draft = null;
function renderPlan() {
  draft = draft || JSON.parse(JSON.stringify({ title: trip.title, date: trip.date, points: trip.points }));
  $('pTitle').value = draft.title; $('pDate').value = draft.date;
  $('pList').innerHTML = draft.points.map((p, i) => `
    <div class="pt" data-i="${i}">
      <label class="full">地点名 <input data-f="name" value="${esc(p.name)}"></label>
      <label class="full">座標（緯度, 経度） <input data-f="ll" inputmode="decimal" value="${p.lat}, ${p.lng}"></label>
      <label>着（予定） <input data-f="arr" type="time" value="${p.arr}" ${i === 0 ? 'disabled' : ''}></label>
      <label>発（予定） <input data-f="dep" type="time" value="${p.dep}" ${i === draft.points.length - 1 ? 'disabled' : ''}></label>
      <div class="ops"><button data-op="up">↑</button><button data-op="down">↓</button><button data-op="del">削除</button></div>
    </div>`).join('');
}
function readPlan() {
  draft.title = $('pTitle').value.trim() || '無題の行程'; draft.date = $('pDate').value || today();
  let ok = true;
  document.querySelectorAll('#pList .pt').forEach((el) => {
    const p = draft.points[+el.dataset.i];
    p.name = el.querySelector('[data-f=name]').value.trim() || '地点';
    const m = el.querySelector('[data-f=ll]').value.match(/(-?\d+(?:\.\d+)?)\s*[,，\s]\s*(-?\d+(?:\.\d+)?)/);
    if (m) { p.lat = +m[1]; p.lng = +m[2]; el.classList.remove('bad'); } else { ok = false; el.classList.add('bad'); }
    p.arr = el.querySelector('[data-f=arr]').value; p.dep = el.querySelector('[data-f=dep]').value;
  });
  return ok;
}
$('pList').onclick = (ev) => {
  const op = ev.target.dataset.op; if (!op) return;
  readPlan();
  const i = +ev.target.closest('.pt').dataset.i, a = draft.points;
  if (op === 'del' && a.length > 2) a.splice(i, 1);
  if (op === 'up' && i > 0) [a[i - 1], a[i]] = [a[i], a[i - 1]];
  if (op === 'down' && i < a.length - 1) [a[i + 1], a[i]] = [a[i], a[i + 1]];
  renderPlan();
};
$('pAdd').onclick = () => { readPlan(); const lp = draft.points[draft.points.length - 1]; draft.points.push({ name: '新しい地点', lat: lp.lat, lng: lp.lng, arr: '', dep: '' }); renderPlan(); };
$('pSample').onclick = () => { const s = sampleTrip(); draft = { title: s.title, date: s.date, points: s.points }; renderPlan(); };
$('pSave').onclick = () => {
  if (!readPlan()) return; // 座標が読めない地点は赤枠にして保存しない
  trip = { title: draft.title, date: draft.date, points: draft.points, log: {} };
  saveTrip(); draft = null; diag(`行程を保存：${trip.title}（${trip.points.length}地点・走行記録はリセット）`);
  if (SIM) simReset();
  document.querySelector('.foot button[data-v=viewRun]').click();
};

// ---- 診断画面（実機確認 T1〜T7 の記録） ----
let diagLog = store.get(LS_DIAG, []);
function diag(msg) {
  const d = new Date();
  diagLog.push(`${d.getMonth() + 1}/${d.getDate()} ${d.getHours()}:${pad(d.getMinutes())}:${pad(d.getSeconds())} ${msg}`);
  if (diagLog.length > 300) diagLog = diagLog.slice(-300);
  store.set(LS_DIAG, diagLog);
}
let wakeState = '未取得';
function renderDiag() {
  const standalone = matchMedia('(display-mode: standalone)').matches || navigator.standalone === true;
  $('diagSummary').innerHTML = [
    ['ホーム画面から起動（T1）', standalone ? 'はい' : 'いいえ（ブラウザで表示中）'],
    ['GPS 取得回数（T2）', `${gps.fixes} 回`],
    ['直近の更新間隔／最大の途切れ', `${gps.lastGapS == null ? '—' : gps.lastGapS.toFixed(1) + ' 秒'} ／ ${gps.maxGapS.toFixed(0)} 秒`],
    ['位置の精度', gps.acc == null ? '—' : `±${Math.round(gps.acc)} m`],
    ['速度（平均）', speedKmh == null ? '—' : `${Math.round(speedKmh)} km/h`],
    ['走行状態', moving ? '走行中' : '停車'],
    ['画面の消灯防止（T3）', wakeState],
    ['GPS エラー', gps.err || 'なし'],
  ].map(([k, v]) => `<b>${k}</b><span>${v}</span>`).join('');
  $('diagLog').textContent = diagLog.slice().reverse().join('\n');
}
$('dCopy').onclick = async () => { try { await navigator.clipboard.writeText(diagLog.join('\n')); $('dCopy').textContent = 'コピーしました'; } catch (e) { $('dCopy').textContent = 'コピーできません'; } };
$('dClear').onclick = () => { diagLog = []; store.set(LS_DIAG, diagLog); renderDiag(); };
$('dReset').onclick = () => { trip.log = {}; saveTrip(); diag('走行記録をリセット'); if (SIM) simReset(); render(); };

// ---- 画面の消灯防止（Wake Lock） ----
let wakeLock = null;
async function keepAwake() {
  if (!('wakeLock' in navigator)) { wakeState = 'この端末は非対応'; return; }
  if (wakeLock || document.visibilityState !== 'visible') return;
  try {
    wakeLock = await navigator.wakeLock.request('screen');
    wakeState = '有効';
    wakeLock.addEventListener('release', () => { wakeLock = null; wakeState = '解除された'; });
  } catch (e) { wakeState = `取得できない（${e.name}）`; }
}
document.addEventListener('visibilitychange', () => {
  diag(document.visibilityState === 'visible' ? '画面に戻った' : '裏に回った（別アプリ表示など）');
  if (document.visibilityState === 'visible') keepAwake();
});
document.addEventListener('click', keepAwake, { once: true });

// ---- GPS（実機） ----
function startGps() {
  if (!('geolocation' in navigator)) { gps.err = 'この端末は位置情報に非対応'; return; }
  navigator.geolocation.watchPosition(
    (p) => onPosition({ lat: p.coords.latitude, lng: p.coords.longitude, acc: p.coords.accuracy, spd: p.coords.speed, ts: p.timestamp }),
    (e) => { gps.err = `${e.code}:${e.message}`; diag(`GPS エラー ${gps.err}`); render(); },
    { enableHighAccuracy: true, maximumAge: 0, timeout: 20000 },
  );
}

// ---- シミュレーション（?sim=1）：行程どおりに走る。道のりは直線×係数、速度は 60km/h 相当 ----
const SIM_KMH = 60;
let simPos = null, simLeg = 0, simArrivedAt = -Infinity;
function simReset() {
  simT = (plannedDep(0) ?? Date.now()) - 2 * 60e3;
  simPos = { lat: P()[0].lat, lng: P()[0].lng }; simLeg = 0; simJamUntil = 0; simArrivedAt = -Infinity;
  pos = null; moving = false; speedKmh = null; nearStopSince = null; nearEnter = null;
}
function simStep(dtMs) {
  simT += dtMs;
  const c = current();
  let spd = 0;
  if (c.mode !== 'finished') {
    // 停車している地点の出発予定時刻を過ぎたら走り出す（遅れて着いても最低90秒は停車し、自動の到着判定を通す）
    const depAt = Math.max(plannedDep(simLeg) ?? simT, simArrivedAt + 90e3);
    const ready = simT >= depAt && simLeg < last();
    if (ready && simT >= simJamUntil) {
      const to = P()[simLeg + 1], d = distM(simPos, to);
      const step = (SIM_KMH / ROUTE_FACTOR / 3.6) * dtMs / 1000; // 直線上の進み
      if (d <= step) { simPos = { lat: to.lat, lng: to.lng }; simLeg++; spd = 0; simArrivedAt = simT; }
      else { const r = step / d; simPos = { lat: simPos.lat + (to.lat - simPos.lat) * r, lng: simPos.lng + (to.lng - simPos.lng) * r }; spd = SIM_KMH / 3.6; }
    }
  }
  onPosition({ lat: simPos.lat, lng: simPos.lng, acc: 5, spd, ts: simT });
}
function startSim() {
  $('simChip').hidden = false; $('simBar').hidden = false;
  simReset();
  // 確認用：?sim=1&jam=20 で出発直後に20分の渋滞を入れる
  const jam = +new URLSearchParams(location.search).get('jam');
  if (jam > 0) simJamUntil = (plannedDep(0) ?? simT) + jam * 60e3;
  document.querySelectorAll('#simBar button[data-x]').forEach((b) => b.onclick = () => {
    simX = +b.dataset.x; document.querySelectorAll('#simBar button[data-x]').forEach((x) => x.classList.toggle('on', x === b));
  });
  $('simPause').onclick = () => { simPaused = !simPaused; $('simPause').textContent = simPaused ? '再開' : '一時停止'; };
  $('simDelay').onclick = () => { simJamUntil = Math.max(simT, simJamUntil) + 10 * 60e3; diag('（模擬）渋滞で10分停止'); };
  setInterval(() => { if (!simPaused) simStep(250 * simX); }, 250);
}

// ---- 起動 ----
if ('serviceWorker' in navigator && location.protocol === 'https:') navigator.serviceWorker.register('sw.js').catch(() => {});
diag(`起動（${SIM ? 'シミュレーション' : '実機GPS'}）`);
if (SIM) startSim(); else startGps();
keepAwake();
setInterval(render, 1000);
render();
// URL 末尾の #plan / #diag で、その画面を開いた状態で起動する
const startView = { '#plan': 'viewPlan', '#diag': 'viewDiag' }[location.hash];
if (startView) document.querySelector(`.foot button[data-v=${startView}]`).click();
