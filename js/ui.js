// Diagram editor + query UI.
import * as M from './model.js';
import { EXAMPLES, exampleById } from './examples.js';
import { prove } from './prover.js';

const SVGNS = 'http://www.w3.org/2000/svg';
const CW = 150, CH = 112, PAD = 70, NODE_H = 36;
const STORE_KEY = 'kt-chaser-v1';

const $ = (id) => document.getElementById(id);
const svg = $('canvas');
const wrap = $('canvasWrap');

let D = M.emptyDiagram();
let sel = { m: new Set(), a: new Set() };
let mode = 'select';
let history = [], future = [];
let query = { type: 'injective' };
let lastResult = null;
// server.mode: 'static' (no server.py, e.g. GitHub Pages), 'nolean' (server.py without a Mathlib project), 'lean'
let server = { ok: false, mode: 'static' };
const RUN_LOCALLY = '#runLocally';
let drag = null;

// ------------------------------------------------------------------ persistence

function save() {
  try { localStorage.setItem(STORE_KEY, JSON.stringify({ diagram: D, query, autoLean: $('autoLean').checked })); } catch { /* storage unavailable */ }
}
function load() {
  try {
    const s = JSON.parse(localStorage.getItem(STORE_KEY) || 'null');
    if (s && s.diagram && Array.isArray(s.diagram.modules)) return s;
  } catch { /* ignore */ }
  return null;
}

function snapshot() { history.push(JSON.stringify(D)); if (history.length > 200) history.shift(); future = []; }
function mutate(fn) { snapshot(); fn(); changed(); }
function changed() { pruneSelection(); render(); renderInspector(); renderHyps(); renderQuery(); save(); }
function undo() { if (!history.length) return; future.push(JSON.stringify(D)); D = JSON.parse(history.pop()); changed(); }
function redo() { if (!future.length) return; history.push(JSON.stringify(D)); D = JSON.parse(future.pop()); changed(); }

function pruneSelection() {
  for (const id of [...sel.m]) if (!M.moduleById(D, id)) sel.m.delete(id);
  for (const id of [...sel.a]) if (!M.arrowById(D, id)) sel.a.delete(id);
}

// ------------------------------------------------------------------ text helpers

const esc = (s) => String(s).replace(/[&<>"]/g, c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;' }[c]));
/** HTML for a math-ish string: _x becomes a subscript */
const mathHTML = (s) => esc(s).replace(/_\(([^)]*)\)|_([A-Za-z0-9'α-ωΑ-Ω₀-₉]+)/g, (m, g1, g2) => `<sub>${g1 || g2}</sub>`);
const modName = (m) => (m.kind === 'zero' ? '0' : m.name);

const measureCtx = document.createElement('canvas').getContext('2d');
function textWidth(s, px = 19) {
  measureCtx.font = `${px}px "STIX Two Math", "Latin Modern Math", "Cambria Math", "Times New Roman", serif`;
  return measureCtx.measureText(s.replace(/_/g, '')).width;
}

function el(tag, attrs = {}, parent = null) {
  const e = document.createElementNS(SVGNS, tag);
  for (const [k, v] of Object.entries(attrs)) e.setAttribute(k, v);
  if (parent) parent.appendChild(e);
  return e;
}

/** fill an svg <text> with a label: "ker f", "ι_f", "A'" */
function setLabel(t, name, { italic = true } = {}) {
  const m = /^(ker|im|coker)\s+(.*)$/.exec(name);
  const add = (s, attrs = {}) => { const sp = el('tspan', attrs, t); sp.textContent = s; return sp; };
  if (m) {
    add(`${m[1]} `, { 'font-style': 'normal' });
    setSub(m[2], true);
    return;
  }
  setSub(name, italic);
  function setSub(s, it) {
    const i = s.indexOf('_');
    const style = it && /^[A-Za-zα-ω]/.test(s) ? 'italic' : 'normal';
    if (i < 0) { add(s, { 'font-style': style }); return; }
    add(s.slice(0, i), { 'font-style': style });
    add(s.slice(i + 1).replace(/^\((.*)\)$/, '$1'), { 'baseline-shift': 'sub', 'font-size': '70%', 'font-style': 'italic' });
  }
}

// ------------------------------------------------------------------ geometry

const cx = (m) => PAD + m.x * CW;
const cy = (m) => PAD + m.y * CH;
function nodeSize(m) {
  const w = Math.max(40, textWidth(modName(m)) + 22 + (m.kind === 'free' ? 10 : 0));
  return { w, h: NODE_H };
}
function nodePos(m) {
  if (drag && drag.kind === 'move' && drag.id === m.id && drag.moved) return { x: drag.px, y: drag.py };
  return { x: cx(m), y: cy(m) };
}
/** exit point of a ray from the node centre in direction (dx, dy) */
function clip(m, dx, dy, gap = 5) {
  const p = nodePos(m), s = nodeSize(m);
  const len = Math.hypot(dx, dy) || 1;
  const ux = dx / len, uy = dy / len;
  const hw = s.w / 2 + gap, hh = s.h / 2 + gap;
  const t = Math.min(ux ? hw / Math.abs(ux) : Infinity, uy ? hh / Math.abs(uy) : Infinity);
  return { x: p.x + ux * t, y: p.y + uy * t };
}

function arrowGeom(a) {
  const A = M.moduleById(D, a.src), B = M.moduleById(D, a.dst);
  const p0 = nodePos(A), p2 = nodePos(B);
  const mx = (p0.x + p2.x) / 2, my = (p0.y + p2.y) / 2;
  const dx = p2.x - p0.x, dy = p2.y - p0.y, len = Math.hypot(dx, dy) || 1;
  const nx = dy / len, ny = -dx / len; // left normal
  const bend = (a.bend || 0) * 34;
  const c = { x: mx + nx * bend, y: my + ny * bend };
  const s = clip(A, c.x - p0.x, c.y - p0.y);
  const e = clip(B, c.x - p2.x, c.y - p2.y, 6);
  const mid = { x: 0.25 * s.x + 0.5 * c.x + 0.25 * e.x, y: 0.25 * s.y + 0.5 * c.y + 0.25 * e.y };
  let side = a.bend ? Math.sign(a.bend) : 1;
  const lab = { x: mid.x + nx * 15 * side, y: mid.y + ny * 15 * side };
  const opp = { x: mid.x - nx * 13 * side, y: mid.y - ny * 13 * side };
  return { s, c, e, lab, opp, nx, ny };
}

// ------------------------------------------------------------------ render canvas

function render() {
  svg.replaceChildren();
  svg.classList.toggle('mode-arrow', mode === 'arrow');
  const maxX = Math.max(5, ...D.modules.map(m => m.x)) + 2;
  const maxY = Math.max(3, ...D.modules.map(m => m.y)) + 2;
  const W = Math.max(PAD * 2 + maxX * CW, wrap.clientWidth), H = Math.max(PAD * 2 + maxY * CH, wrap.clientHeight - 4);
  svg.setAttribute('width', W); svg.setAttribute('height', H);
  el('rect', { x: 0, y: 0, width: W, height: H, fill: 'transparent', 'data-bg': '1' }, svg);
  const g0 = el('g', {}, svg);
  for (let i = 0; PAD + i * CW < W; i++) for (let j = 0; PAD + j * CH < H; j++) {
    el('circle', { cx: PAD + i * CW, cy: PAD + j * CH, r: 1.6, class: 'grid-dot' }, g0);
  }
  const ga = el('g', {}, svg);
  for (const a of D.arrows) drawArrow(ga, a);
  const gx = el('g', {}, svg);
  for (const e of D.exact) drawExact(gx, e);
  for (const s of D.squares) drawCorner(gx, s);
  const gn = el('g', {}, svg);
  for (const m of D.modules) drawNode(gn, m);
  if (drag && drag.kind === 'arrow' && drag.moved) {
    const A = M.moduleById(D, drag.id);
    const s = clip(A, drag.px - cx(A), drag.py - cy(A));
    el('path', { d: `M${s.x},${s.y} L${drag.px},${drag.py}`, class: 'ghost' }, svg);
  }
  $('canvasHint').hidden = D.modules.length > 1 && D.arrows.length > 0;
}

function drawNode(g, m) {
  const p = nodePos(m), s = nodeSize(m);
  const cls = ['node', m.kind, m.construct ? 'construct' : '', sel.m.has(m.id) ? 'selected' : '', drag && drag.hover === m.id ? 'hover-target' : ''].join(' ');
  const n = el('g', { class: cls, 'data-node': m.id, transform: `translate(${p.x},${p.y})` }, g);
  el('rect', { x: -s.w / 2, y: -s.h / 2, width: s.w, height: s.h, rx: 7 }, n);
  const t = el('text', { x: m.kind === 'free' ? -5 : 0, y: 0 }, n);
  setLabel(t, modName(m), { italic: true });
  if (m.kind === 'free') {
    const b = el('text', { x: s.w / 2 - 9, y: -s.h / 2 + 9, class: 'badge' }, n);
    b.textContent = 'F';
  }
  const title = el('title', {}, n);
  title.textContent = `${modName(m)} — ${m.kind === 'zero' ? 'zero module' : m.kind === 'free' ? 'free module' : 'module'}${m.construct ? ` (${m.construct.type})` : ''}`;
}

function drawArrow(g, a) {
  const G = arrowGeom(a);
  const cls = ['arrow', a.dashed ? 'dashed' : '', a.equal ? 'equal' : '', a.auto ? 'auto' : '', sel.a.has(a.id) ? 'selected' : ''].join(' ');
  const ag = el('g', { class: cls, 'data-arrow': a.id }, g);
  const d = `M${G.s.x},${G.s.y} Q${G.c.x},${G.c.y} ${G.e.x},${G.e.y}`;
  const S = M.moduleById(D, a.src), T = M.moduleById(D, a.dst);
  if (a.equal) {
    // identity: a double line without head or label, as in A ═ A
    const off = 2.1, e0 = clip(T, G.c.x - nodePos(T).x, G.c.y - nodePos(T).y);
    for (const k of [-1, 1]) {
      const o = (p) => ({ x: p.x + G.nx * off * k, y: p.y + G.ny * off * k });
      const s0 = o(G.s), c0 = o(G.c), t0 = o(e0);
      el('path', { d: `M${s0.x},${s0.y} Q${c0.x},${c0.y} ${t0.x},${t0.y}`, class: 'line' }, ag);
    }
    el('path', { d, class: 'hit' }, ag);
    el('title', {}, ag).textContent = `${modName(S)} = ${modName(T)} (the same module; ${a.name} is the identity)`;
    return;
  }
  el('path', { d, class: 'line' }, ag);
  // head
  const hx = G.e.x - G.c.x, hy = G.e.y - G.c.y, hl = Math.hypot(hx, hy) || 1;
  const ux = hx / hl, uy = hy / hl;
  const head = (bx, by) => {
    const L = 9, W = 5.2;
    return `M${bx - ux * L + uy * W},${by - uy * L - ux * W} L${bx},${by} L${bx - ux * L - uy * W},${by - uy * L + ux * W}`;
  };
  const iso = a.mono && a.epi;
  let hd = head(G.e.x, G.e.y);
  if (a.epi && !iso) hd += ' ' + head(G.e.x - ux * 5.5, G.e.y - uy * 5.5);
  if (a.mono && !iso) {
    // hook at the tail
    const tx = G.c.x - G.s.x, ty = G.c.y - G.s.y, tl = Math.hypot(tx, ty) || 1;
    const vx = tx / tl, vy = ty / tl;
    const r = 4.2;
    const px = -vy, py = vx;
    const sx = G.s.x, sy = G.s.y;
    hd += ` M${sx},${sy} A${r},${r} 0 0 ${a.bend < 0 ? 0 : 1} ${sx + px * 2 * r},${sy + py * 2 * r}`;
  }
  el('path', { d: hd, class: 'head' }, ag);
  el('path', { d, class: 'hit' }, ag);
  const t = el('text', { x: G.lab.x, y: G.lab.y }, ag);
  setLabel(t, a.name, { italic: true });
  const tags = [];
  if (a.mono && a.epi) tags.push('≅');
  if (a.zero) tags.push('0');
  if (a.dashed) tags.push('∃!');
  if (tags.length) {
    const tt = el('text', { x: G.opp.x, y: G.opp.y, class: 'tag' }, ag);
    tt.textContent = tags.join(' ');
  }
  const title = el('title', {}, ag);
  title.textContent = `${a.name} : ${modName(S)} → ${modName(T)}${a.mono && a.epi ? ' (isomorphism)' : a.mono ? ' (injective)' : a.epi ? ' (surjective)' : ''}${a.zero ? ' (zero map)' : ''}${a.dashed ? ' (induced ∃!)' : ''}`;
}

function drawExact(g, e) {
  const f = M.arrowById(D, e.first), h = M.arrowById(D, e.second);
  if (!f || !h) return;
  const B = M.moduleById(D, f.dst);
  const p = nodePos(B), s = nodeSize(B);
  const ang = (a) => { const G = arrowGeom(a); return Math.atan2(G.c.y - p.y, G.c.x - p.x); };
  const t1 = ang(f), t2 = ang(h);
  const norm2 = (x) => { while (x < 0) x += 2 * Math.PI; while (x >= 2 * Math.PI) x -= 2 * Math.PI; return x; };
  // two sides between the directions of f and h; pick the one with fewer other maps at B
  const ccw = norm2(t2 - t1);
  const sides = [
    { mid: t1 + ccw / 2, from: t1, span: ccw },
    { mid: t1 - (2 * Math.PI - ccw) / 2, from: t2, span: 2 * Math.PI - ccw },
  ];
  const others = D.arrows.filter(a => a !== f && a !== h && (a.src === B.id || a.dst === B.id)).map(ang);
  for (const sd of sides) sd.n = others.filter(o => norm2(o - sd.from) < sd.span).length;
  sides.sort((x, y) => x.n - y.n || Math.sin(y.mid) - Math.sin(x.mid));
  const mid = sides[0].mid;
  const rx = s.w / 2 + 7, ry = s.h / 2 + 7, half = 0.5;
  const P = (t) => ({ x: p.x + rx * Math.cos(t), y: p.y + ry * Math.sin(t) });
  const q1 = P(mid - half), q2 = P(mid + half);
  const arc = el('path', { d: `M${q1.x},${q1.y} A${rx},${ry} 0 0 1 ${q2.x},${q2.y}`, class: 'exact-arc' }, g);
  el('title', {}, arc).textContent = `exact at ${modName(B)}: ${f.name}, ${h.name}`;
}

function drawCorner(g, s) {
  const a1 = M.arrowById(D, s.a1), a2 = M.arrowById(D, s.a2), b1 = M.arrowById(D, s.b1);
  if (!a1 || !a2 || !b1) return;
  const P = M.moduleById(D, a1.src), X1 = M.moduleById(D, a1.dst), X2 = M.moduleById(D, a2.dst), T = M.moduleById(D, b1.dst);
  const corner = s.type === 'pullback' ? P : T;
  const pc = nodePos(corner), pu = nodePos(X1), pv = nodePos(X2);
  const du = norm(pu.x - pc.x, pu.y - pc.y), dv = norm(pv.x - pc.x, pv.y - pc.y);
  const o = { x: pc.x + (du.x + dv.x) * 26, y: pc.y + (du.y + dv.y) * 26 };
  const L = 9;
  const path = el('path', {
    d: `M${o.x + du.x * L},${o.y + du.y * L} L${o.x + (du.x + dv.x) * L},${o.y + (du.y + dv.y) * L} L${o.x + dv.x * L},${o.y + dv.y * L}`,
    class: 'corner',
  }, g);
  el('title', {}, path).textContent = s.type;
}
function norm(x, y) { const l = Math.hypot(x, y) || 1; return { x: x / l, y: y / l }; }

// ------------------------------------------------------------------ pointer interaction

function svgPoint(ev) {
  const r = svg.getBoundingClientRect();
  return { x: ev.clientX - r.left, y: ev.clientY - r.top };
}
function nodeAt(pt) {
  for (const m of D.modules) {
    const s = nodeSize(m);
    if (Math.abs(pt.x - cx(m)) <= s.w / 2 + 4 && Math.abs(pt.y - cy(m)) <= s.h / 2 + 4) return m;
  }
  return null;
}
function cellAt(pt) {
  return { x: Math.max(0, Math.round((pt.x - PAD) / CW)), y: Math.max(0, Math.round((pt.y - PAD) / CH)) };
}

// double-clicks are detected by hand: every click re-renders the SVG, so the
// browser's own dblclick (which needs the same target element) is unreliable.
let lastClick = { t: 0, x: 0, y: 0, key: '' };
function isDouble(key, pt) {
  const now = performance.now();
  const dbl = key === lastClick.key && now - lastClick.t < 450 && Math.hypot(pt.x - lastClick.x, pt.y - lastClick.y) < 8;
  lastClick = dbl ? { t: 0, x: 0, y: 0, key: '' } : { t: now, x: pt.x, y: pt.y, key };
  return dbl;
}

function focusName() {
  const inp = $('nameInput');
  if (inp && !inp.disabled) { inp.focus(); inp.select(); }
}

svg.addEventListener('pointerdown', (ev) => {
  if (ev.button !== 0) return;
  const pt = svgPoint(ev);
  const nodeEl = ev.target.closest('[data-node]');
  const arrowEl = ev.target.closest('[data-arrow]');
  if (nodeEl) {
    const id = nodeEl.getAttribute('data-node');
    drag = { kind: mode === 'arrow' || ev.shiftKey ? 'arrow' : 'move', id, x0: pt.x, y0: pt.y, px: pt.x, py: pt.y, moved: false, shift: ev.shiftKey };
    svg.setPointerCapture(ev.pointerId);
    return;
  }
  if (arrowEl) {
    const id = arrowEl.getAttribute('data-arrow');
    const dbl = isDouble(`a:${id}`, pt);
    if (ev.shiftKey || ev.metaKey || ev.ctrlKey) { sel.a.has(id) ? sel.a.delete(id) : sel.a.add(id); }
    else { sel = { m: new Set(), a: new Set([id]) }; }
    render(); renderInspector();
    if (dbl) focusName();
    return;
  }
  if (isDouble('bg', pt)) {
    const c = cellAt(pt);
    if (M.cellFree(D, c.x, c.y)) {
      mutate(() => {
        const m = M.addModule(D, { x: c.x, y: c.y });
        sel = { m: new Set([m.id]), a: new Set() };
      });
    }
    return;
  }
  if (!ev.shiftKey && (sel.m.size || sel.a.size)) { sel = { m: new Set(), a: new Set() }; render(); renderInspector(); }
});

svg.addEventListener('pointermove', (ev) => {
  if (!drag) return;
  const pt = svgPoint(ev);
  drag.px = pt.x; drag.py = pt.y;
  if (!drag.moved && Math.hypot(pt.x - drag.x0, pt.y - drag.y0) > 4) drag.moved = true;
  if (!drag.moved) return;
  if (drag.kind === 'arrow') {
    const h = nodeAt(pt);
    drag.hover = h && h.id !== drag.id ? h.id : null;
  }
  render();
});

svg.addEventListener('pointerup', (ev) => {
  if (!drag) return;
  const d = drag;
  drag = null;
  const pt = svgPoint(ev);
  if (!d.moved) {
    // click on a node: select (double-click: edit its name)
    const dbl = isDouble(`m:${d.id}`, pt);
    if (d.shift || ev.metaKey || ev.ctrlKey) { sel.m.has(d.id) ? sel.m.delete(d.id) : sel.m.add(d.id); }
    else sel = { m: new Set([d.id]), a: new Set() };
    render(); renderInspector();
    if (dbl) focusName();
    return;
  }
  if (d.kind === 'move') {
    const c = cellAt(pt);
    const m = M.moduleById(D, d.id);
    if ((c.x !== m.x || c.y !== m.y) && M.cellFree(D, c.x, c.y)) mutate(() => { m.x = c.x; m.y = c.y; });
    else render();
    return;
  }
  const target = nodeAt(pt);
  if (target && target.id !== d.id) {
    mutate(() => {
      const n = D.arrows.filter(a => (a.src === d.id && a.dst === target.id) || (a.src === target.id && a.dst === d.id)).length;
      const bend = n === 0 ? 0 : (n % 2 ? 1 : -1) * Math.ceil(n / 2);
      const a = M.addArrow(D, { src: d.id, dst: target.id, bend });
      sel = { m: new Set(), a: new Set([a.id]) };
    });
  } else render();
});

document.addEventListener('keydown', (ev) => {
  const inField = /INPUT|SELECT|TEXTAREA/.test(document.activeElement.tagName);
  if ((ev.metaKey || ev.ctrlKey) && ev.key.toLowerCase() === 'z' && !inField) {
    ev.preventDefault(); ev.shiftKey ? redo() : undo(); return;
  }
  if (inField) return;
  if (ev.key === 'Delete' || ev.key === 'Backspace') { ev.preventDefault(); deleteSelection(); }
  else if (ev.key === 'Escape') { drag = null; sel = { m: new Set(), a: new Set() }; render(); renderInspector(); }
  else if (ev.key === 'a' || ev.key === 'A') setMode('arrow');
  else if (ev.key === 'v' || ev.key === 'V') setMode('select');
});

function deleteSelection() {
  if (!sel.m.size && !sel.a.size) return;
  mutate(() => { M.deleteItems(D, { modules: [...sel.m], arrows: [...sel.a] }); sel = { m: new Set(), a: new Set() }; });
}

function setMode(m) {
  mode = m;
  $('modeSelect').classList.toggle('active', m === 'select');
  $('modeArrow').classList.toggle('active', m === 'arrow');
  render();
}

// ------------------------------------------------------------------ inspector

function h(html) { const t = document.createElement('template'); t.innerHTML = html.trim(); return t.content; }

function renderInspector() {
  const box = $('inspector');
  const ms = [...sel.m].map(id => M.moduleById(D, id)).filter(Boolean);
  const as = [...sel.a].map(id => M.arrowById(D, id)).filter(Boolean);
  box.replaceChildren();
  if (!ms.length && !as.length) {
    box.append(h(`<h2>Selection</h2><p class="muted small">Nothing selected. ${D.modules.length} modules, ${D.arrows.length} maps.
      Double-click the grid to add a module; <span class="kbd">Shift</span>-drag between modules to add a map; <span class="kbd">Shift</span>-click maps to select several.</p>`));
    return;
  }
  if (ms.length === 1 && !as.length) return inspectModule(box, ms[0]);
  if (as.length === 1 && !ms.length) return inspectArrow(box, as[0]);
  if (as.length > 1 && !ms.length) return inspectArrows(box, as);
  box.append(h(`<h2>Selection</h2><p>${ms.length} modules, ${as.length} maps selected.</p><div class="row"><button id="delSel">Delete</button></div>`));
  $('delSel').onclick = deleteSelection;
}

function inspectModule(box, m) {
  const con = m.construct ? M.arrowById(D, m.construct.arrow) : null;
  box.append(h(`<h2>Module</h2>
    <label class="field"><span>Name ${m.construct ? '(set by the construction)' : '(upper case)'}</span>
      <input id="nameInput" type="text" value="${esc(modName(m))}" ${m.construct || m.kind === 'zero' ? 'disabled' : ''} autocomplete="off" spellcheck="false"></label>
    <div class="field"><span>Kind</span><div class="row">
      ${['general', 'free', 'zero'].map(k => `<label class="check"><input type="radio" name="kind" value="${k}" ${m.kind === k ? 'checked' : ''} ${m.construct ? 'disabled' : ''}> ${k === 'zero' ? '0' : k}</label>`).join('')}
    </div></div>
    ${M.equalClass(D, m.id).length > 1 ? `<p class="small muted">Identified by “=” with ${M.equalClass(D, m.id).filter(x => x !== m).map(x => `<span class="math">${mathHTML(modName(x))}</span>`).join(', ')}: the same module (kind changes apply to all).</p>` : ''}
    ${con ? `<p class="small muted">The ${{ ker: 'kernel', im: 'image', coker: 'cokernel' }[m.construct.type]} of <span class="math">${mathHTML(con.name)}</span>, characterised by its universal map(s) and exactness.</p>` : ''}
    <p class="small muted" id="nameWarn"></p>
    <div class="row"><button id="qZero">Is it 0?</button><button id="delBtn">Delete</button></div>`));
  const inp = $('nameInput');
  inp.addEventListener('change', () => {
    const v = inp.value.trim();
    if (!v) { inp.value = m.name; return; }
    mutate(() => { m.name = v; });
  });
  inp.addEventListener('input', () => {
    const v = inp.value.trim();
    $('nameWarn').textContent = v && !/^[A-Z]/.test(v) ? 'Convention: module names start with an upper-case letter.' : '';
  });
  box.querySelectorAll('input[name=kind]').forEach(r => r.addEventListener('change', () => mutate(() => {
    M.setKind(D, m.id, r.value);
    if (m.kind === 'zero') m.name = m.name || '0';
  })));
  $('delBtn').onclick = deleteSelection;
  $('qZero').onclick = () => runQuickQuery({ type: 'subset', lhsKind: 'all', lhsModule: m.id, rhsKind: 'zero', rhsModule: m.id });
}

function inspectArrow(box, a) {
  const S = M.moduleById(D, a.src), T = M.moduleById(D, a.dst);
  const has = (t) => D.modules.some(m => m.construct && m.construct.type === t && m.construct.arrow === a.id);
  const lock = a.dashed || a.auto || a.equal ? 'disabled' : '';
  box.append(h(`<h2>Map</h2>
    <label class="field"><span>Name (lower case)</span>
      <input id="nameInput" type="text" value="${esc(a.name)}" ${a.auto ? 'disabled' : ''} autocomplete="off" spellcheck="false"></label>
    <p class="math" style="margin:0 0 8px;font-size:16px">${a.equal ? `${mathHTML(modName(S))} = ${mathHTML(modName(T))}` : `${mathHTML(a.name)} : ${mathHTML(modName(S))} → ${mathHTML(modName(T))}`}</p>
    ${a.composite ? `<p class="small muted" style="margin:-4px 0 8px">Defined as the composite <span class="math">${mathHTML(M.compositeName(D, a.composite))}</span> (equal to it by commutativity).</p>` : ''}
    <div class="field"><span>Hypotheses on this map</span><div class="row">
      <label class="check"><input type="checkbox" id="pMono" ${a.mono ? 'checked' : ''} ${lock}> injective ↪</label>
      <label class="check"><input type="checkbox" id="pEpi" ${a.epi ? 'checked' : ''} ${lock}> surjective ↠</label>
      <label class="check"><input type="checkbox" id="pIso" ${a.mono && a.epi ? 'checked' : ''} ${lock}> isomorphism ≅</label>
      <label class="check"><input type="checkbox" id="pZero" ${a.zero ? 'checked' : ''} ${lock}> zero</label>
    </div>
    <label class="check" style="margin-top:6px" title="The target is the same module as the source and this map is its identity. Stronger than ≅: an isomorphism is some invertible map between possibly different modules."><input type="checkbox" id="pEqual" ${a.equal ? 'checked' : ''} ${a.auto || a.dashed ? 'disabled' : ''}> identity = (same module)</label>
    <label class="check" style="margin-top:6px"><input type="checkbox" id="pDashed" ${a.dashed ? 'checked' : ''} ${a.auto || a.equal ? 'disabled' : ''}> induced ∃! (dashed: to be constructed from the diagram)</label>
    </div>
    <p class="small muted" id="nameWarn">${a.equal ? `${esc(modName(S))} and ${esc(modName(T))} are the same module and ${esc(a.name)} is its identity map.` : a.mono && a.epi ? 'Injective and surjective: an isomorphism (possibly between different modules; use “=” to identify them).' : ''}</p>
    <div class="row">${a.equal ? '' : `<span class="small muted">Add</span>
      <button id="cKer" ${has('ker') ? 'disabled' : ''}>ker</button>
      <button id="cIm" ${has('im') ? 'disabled' : ''}>im</button>
      <button id="cCoker" ${has('coker') ? 'disabled' : ''}>coker</button>`}
      <span class="small muted">Curve</span><button id="bendL" title="Curve left">↶</button><button id="bendR" title="Curve right">↷</button>
      ${a.equal ? '<button id="flipEq" title="The direction of = carries no meaning; reversing it can break a directed cycle">Reverse</button>' : ''}
    </div>
    ${a.equal ? '' : `<div class="row"><span class="small muted">Ask</span>
      ${a.dashed ? '<button id="qInd">exists?</button>' : ''}
      <button id="qInj">injective?</button><button id="qSurj">surjective?</button><button id="qIso">iso?</button><button id="qZ">zero?</button>
    </div>`}
    <div class="row"><button id="delBtn">Delete</button></div>`));
  const inp = $('nameInput');
  inp.addEventListener('change', () => {
    const v = inp.value.trim();
    if (!v) { inp.value = a.name; return; }
    mutate(() => M.renameArrow(D, a.id, v));
  });
  inp.addEventListener('input', () => {
    const v = inp.value.trim();
    $('nameWarn').textContent = v && /^[A-Z]/.test(v) ? 'Convention: map names start with a lower-case letter.' : '';
  });
  $('pMono').onchange = (e) => mutate(() => { a.mono = e.target.checked; });
  $('pEpi').onchange = (e) => mutate(() => { a.epi = e.target.checked; });
  $('pIso').onchange = (e) => mutate(() => { a.mono = a.epi = e.target.checked; });
  $('pZero').onchange = (e) => mutate(() => { a.zero = e.target.checked; });
  $('pEqual').onchange = (e) => mutate(() => M.setEqual(D, a.id, e.target.checked));
  $('pDashed').onchange = (e) => mutate(() => {
    a.dashed = e.target.checked;
    if (a.dashed) {
      a.mono = a.epi = a.zero = false;
      D.exact = D.exact.filter(x => x.first !== a.id && x.second !== a.id);
      D.squares = D.squares.filter(s => ![s.a1, s.a2, s.b1, s.b2].includes(a.id));
    }
  });
  const con = (t) => mutate(() => { const m = M.addConstruction(D, t, a.id); sel = { m: new Set([m.id]), a: new Set() }; });
  if (!a.equal) {
    $('cKer').onclick = () => con('ker');
    $('cIm').onclick = () => con('im');
    $('cCoker').onclick = () => con('coker');
  } else {
    $('flipEq').onclick = () => mutate(() => M.reverseEqual(D, a.id));
  }
  $('bendL').onclick = () => mutate(() => { a.bend = (a.bend || 0) + 1; });
  $('bendR').onclick = () => mutate(() => { a.bend = (a.bend || 0) - 1; });
  $('delBtn').onclick = deleteSelection;
  const key = `a:${a.id}`;
  if (a.equal) return;
  if (a.dashed) $('qInd').onclick = () => runQuickQuery({ type: 'induced', arrow: a.id });
  $('qInj').onclick = () => runQuickQuery({ type: 'injective', map1: key });
  $('qSurj').onclick = () => runQuickQuery({ type: 'surjective', map1: key });
  $('qIso').onclick = () => runQuickQuery({ type: 'iso', map1: key });
  $('qZ').onclick = () => runQuickQuery({ type: 'zero', map1: key });
}

function inspectArrows(box, as) {
  const ids = as.map(a => a.id);
  const chain = M.chainOrder(D, ids);
  const sq = M.squareShape(D, ids);
  const names = (chain || ids).map(id => mathHTML(M.arrowById(D, id).name)).join(', ');
  box.append(h(`<h2>${as.length} maps</h2>
    <p class="math" style="margin:0 0 8px;font-size:16px">${names}</p>
    <div class="row">
      ${chain ? `<button id="mExact">Mark exact${chain.length > 2 ? ' (whole chain)' : ''}</button>` : ''}
      ${chain ? `<button id="mComp" title="Add a map equal to the composite">Add composite ${esc(M.compositeName(D, chain))}</button>` : ''}
      ${sq ? '<button id="mPB">Pullback square</button><button id="mPO">Pushout square</button>' : ''}
      <button id="delBtn">Delete</button>
    </div>
    ${chain && chain.length === 2 ? '<div class="row"><span class="small muted">Ask</span><button id="qEx">exact?</button><button id="qComp">composite zero?</button></div>' : ''}
    ${!chain && !sq ? '<p class="small muted">Select a composable chain to mark it exact, or four maps forming a square for pullback/pushout.</p>' : ''}`));
  if (chain) $('mExact').onclick = () => mutate(() => { M.addExactChain(D, chain); });
  if (chain) $('mComp').onclick = () => {
    const first = M.arrowById(D, chain[0]), last = M.arrowById(D, chain[chain.length - 1]);
    if (first.src === last.dst) { alert('The composite would be a loop (an endomorphism), which the chaser does not support.'); return; }
    mutate(() => { const c = M.addComposite(D, chain); if (c) sel = { m: new Set(), a: new Set([c.id]) }; });
  };
  if (sq) {
    $('mPB').onclick = () => mutate(() => { M.addSquare(D, 'pullback', sq); });
    $('mPO').onclick = () => mutate(() => { M.addSquare(D, 'pushout', sq); });
  }
  if (chain && chain.length === 2) {
    $('qEx').onclick = () => runQuickQuery({ type: 'exact', map1: `a:${chain[0]}`, map2: `a:${chain[1]}` });
    $('qComp').onclick = () => runQuickQuery({ type: 'zero', map1: `p:${chain.join(',')}` });
  }
  $('delBtn').onclick = deleteSelection;
}

// ------------------------------------------------------------------ hypotheses panel

function renderHyps() {
  const box = $('hypList');
  box.replaceChildren();
  const items = [];
  for (const e of D.exact) {
    const f = M.arrowById(D, e.first), g = M.arrowById(D, e.second);
    if (!f || !g) continue;
    items.push({ html: `exact at <span class="math">${mathHTML(modName(M.moduleById(D, f.dst)))}</span>: <span class="math">${mathHTML(f.name)}, ${mathHTML(g.name)}</span>`, del: () => mutate(() => { D.exact = D.exact.filter(x => x !== e); }), auto: !!e.auto });
  }
  for (const s of D.squares) {
    const n = [s.a1, s.a2, s.b1, s.b2].map(id => M.arrowById(D, id)).filter(Boolean).map(a => mathHTML(a.name)).join(', ');
    items.push({ html: `${s.type}: <span class="math">${n}</span>`, del: () => mutate(() => { D.squares = D.squares.filter(x => x !== s); }) });
  }
  const props = D.arrows.filter(a => !a.auto && !a.equal && (a.mono || a.epi || a.zero)).map(a => `<span class="math">${mathHTML(a.name)}</span> ${a.mono && a.epi ? '≅' : a.mono ? '↪' : a.epi ? '↠' : ''}${a.zero ? ' = 0' : ''}`);
  const equals = D.arrows.filter(a => a.equal).map(a => `<span class="math">${mathHTML(modName(M.moduleById(D, a.src)))} = ${mathHTML(modName(M.moduleById(D, a.dst)))}</span>`);
  const frees = D.modules.filter(m => m.kind === 'free').map(m => `<span class="math">${mathHTML(m.name)}</span>`);
  if (!items.length && !props.length && !frees.length && !equals.length) {
    box.append(h('<p class="muted small">No hypotheses yet besides commutativity. Mark maps injective/surjective, and select chains to mark them exact.</p>'));
    return;
  }
  if (props.length) box.append(h(`<p class="small" style="margin:0 0 6px">Maps: ${props.join(' · ')}</p>`));
  if (equals.length) box.append(h(`<p class="small" style="margin:0 0 6px" title="Identified modules: the same module, joined by its identity map">Identified: ${equals.join(' · ')}</p>`));
  if (frees.length) box.append(h(`<p class="small" style="margin:0 0 6px">Free: ${frees.join(', ')}</p>`));
  const chips = document.createElement('div');
  chips.className = 'chips';
  for (const it of items) {
    const c = h(`<span class="chip">${it.html}${it.auto ? ' <span class="muted small">(auto)</span>' : ''}<button class="x" title="Remove" aria-label="Remove">×</button></span>`);
    c.querySelector('.x').onclick = it.del;
    chips.append(c);
  }
  box.append(chips);
  box.append(h('<p class="muted small" style="margin:8px 0 0">The whole diagram is assumed to commute.</p>'));
}

// ------------------------------------------------------------------ queries

const QTYPES = [
  ['injective', 'map is injective'], ['surjective', 'map is surjective'], ['iso', 'map is an isomorphism'], ['zero', 'map is zero'],
  ['exact', 'sequence is exact'], ['subset', 'submodule inclusion ⊆'], ['equal', 'submodule equality ='],
  ['existsMap', 'there is an injective/surjective/iso map'], ['induced', 'induced map ∃! exists'],
];

function allPaths(maxLen = 4, limit = 80) {
  const out = [];
  const outArrows = new Map();
  for (const a of D.arrows) { if (!outArrows.has(a.src)) outArrows.set(a.src, []); outArrows.get(a.src).push(a); }
  const walk = (path, seen) => {
    if (out.length >= limit) return;
    if (path.length >= 2) out.push(path.slice());
    if (path.length >= maxLen) return;
    const last = path[path.length - 1];
    for (const b of outArrows.get(last.dst) || []) {
      if (seen.has(b.dst)) continue;
      path.push(b); seen.add(b.dst);
      walk(path, seen);
      path.pop(); seen.delete(b.dst);
    }
  };
  for (const a of D.arrows) walk([a], new Set([a.src, a.dst]));
  return out;
}

function mapOptions(selected) {
  const opts = [];
  const lab = (arr) => `${arr.slice().reverse().map(a => a.name).join('∘')} : ${modName(M.moduleById(D, arr[0].src))} → ${modName(M.moduleById(D, arr[arr.length - 1].dst))}`;
  for (const a of D.arrows) opts.push([`a:${a.id}`, lab([a])]);
  const comps = allPaths();
  let html = '<option value="">choose a map…</option>';
  html += opts.map(([v, l]) => `<option value="${v}" ${v === selected ? 'selected' : ''}>${esc(l)}</option>`).join('');
  if (comps.length) {
    html += '<optgroup label="Composites">';
    html += comps.map(p => { const v = `p:${p.map(a => a.id).join(',')}`; return `<option value="${v}" ${v === selected ? 'selected' : ''}>${esc(lab(p))}</option>`; }).join('');
    html += '</optgroup>';
  }
  return html;
}
function moduleOptions(selected) {
  return '<option value="">choose a module…</option>' + D.modules.map(m => `<option value="${m.id}" ${m.id === selected ? 'selected' : ''}>${esc(modName(m))}</option>`).join('');
}
function pathOf(key) {
  if (!key) return null;
  return key.startsWith('a:') ? [key.slice(2)] : key.slice(2).split(',');
}

function renderQuery() {
  const box = $('queryForm');
  const q = query;
  box.replaceChildren();
  const typeSel = `<div class="qrow"><select id="qType" aria-label="Query type">${QTYPES.map(([v, l]) => `<option value="${v}" ${q.type === v ? 'selected' : ''}>${l}</option>`).join('')}</select></div>`;
  let body = '';
  const subRow = (side) => {
    const kind = q[`${side}Kind`] || 'ker';
    const needsMap = kind === 'ker' || kind === 'im';
    return `<div class="qrow"><select id="${side}Kind" aria-label="${side} kind">
      ${[['ker', 'ker'], ['im', 'im'], ['zero', '0'], ['all', 'whole module']].map(([v, l]) => `<option value="${v}" ${kind === v ? 'selected' : ''}>${l}</option>`).join('')}
      </select>${needsMap ? `<select id="${side}Map" aria-label="${side} map">${mapOptions(q[`${side}Map`])}</select>` : `<select id="${side}Module" aria-label="${side} module">${moduleOptions(q[`${side}Module`])}</select>`}</div>`;
  };
  switch (q.type) {
    case 'injective': case 'surjective': case 'iso': case 'zero':
      body = `<div class="qrow"><select id="map1" aria-label="Map">${mapOptions(q.map1)}</select></div>`; break;
    case 'exact':
      body = `<div class="qrow"><select id="map1" aria-label="First map">${mapOptions(q.map1)}</select></div><div class="qrow"><select id="map2" aria-label="Second map">${mapOptions(q.map2)}</select></div><p class="small muted">Exactness at the middle module: ker(second) = im(first).</p>`; break;
    case 'subset': case 'equal':
      body = `${subRow('lhs')}<div class="qrow"><span class="rel">${q.type === 'subset' ? '⊆' : '='}</span></div>${subRow('rhs')}<p class="small muted">Both sides must be submodules of the same module (ker of maps out of it, im of maps into it).</p>`; break;
    case 'existsMap':
      body = `<div class="qrow"><select id="prop" aria-label="Property">${['injective', 'surjective', 'iso'].map(p => `<option value="${p}" ${q.prop === p ? 'selected' : ''}>${p === 'iso' ? 'isomorphism' : p}</option>`).join('')}</select></div>
        <div class="qrow"><select id="from" aria-label="From">${moduleOptions(q.from)}</select><span class="rel">→</span><select id="to" aria-label="To">${moduleOptions(q.to)}</select></div>
        <p class="small muted">Tests the map given by the diagram (all composites agree by commutativity). Draw a dashed ∃! map to test an induced one.</p>`; break;
    case 'induced':
      body = `<div class="qrow"><select id="arrowSel" aria-label="Induced map"><option value="">choose a dashed map…</option>${D.arrows.filter(a => a.dashed).map(a => `<option value="${a.id}" ${q.arrow === a.id ? 'selected' : ''}>${esc(a.name)} : ${esc(modName(M.moduleById(D, a.src)))} → ${esc(modName(M.moduleById(D, a.dst)))}</option>`).join('')}</select></div>`; break;
    default: break;
  }
  box.append(h(typeSel + body));
  const bind = (id, key) => { const e = $(id); if (e) e.onchange = () => { query[key] = e.value; save(); if (/Kind$/.test(id)) renderQuery(); }; };
  $('qType').onchange = (e) => { query = { ...query, type: e.target.value }; save(); renderQuery(); };
  ['map1', 'map2', 'lhsKind', 'lhsMap', 'lhsModule', 'rhsKind', 'rhsMap', 'rhsModule', 'from', 'to', 'prop'].forEach(k => bind(k, k));
  bind('arrowSel', 'arrow');
}

function buildQuery(q) {
  const need = (v, what) => { if (!v) throw new Error(`Choose ${what}.`); return v; };
  switch (q.type) {
    case 'injective': case 'surjective': case 'iso': case 'zero':
      return { type: q.type, path: pathOf(need(q.map1, 'a map')) };
    case 'exact':
      return { type: 'exact', first: pathOf(need(q.map1, 'the first map')), second: pathOf(need(q.map2, 'the second map')) };
    case 'subset': case 'equal': {
      const side = (s) => {
        const kind = q[`${s}Kind`] || 'ker';
        if (kind === 'ker' || kind === 'im') return { kind, path: pathOf(need(q[`${s}Map`], 'a map')) };
        return { kind, module: need(q[`${s}Module`] || ambientGuess(q), 'a module') };
      };
      return { type: q.type, lhs: side('lhs'), rhs: side('rhs') };
    }
    case 'existsMap': return { type: 'existsMap', from: need(q.from, 'a source module'), to: need(q.to, 'a target module'), prop: q.prop || 'injective' };
    case 'induced': return { type: 'induced', arrow: need(q.arrow, 'a dashed map') };
    default: throw new Error('Unknown query.');
  }
}

/** for 0 / whole-module sides, default to the ambient module of the other side */
function ambientGuess(q) {
  for (const s of ['lhs', 'rhs']) {
    const kind = q[`${s}Kind`];
    const p = pathOf(q[`${s}Map`]);
    if ((kind === 'ker' || kind === 'im') && p) {
      const a = M.arrowById(D, kind === 'ker' ? p[0] : p[p.length - 1]);
      if (a) return kind === 'ker' ? a.src : a.dst;
    }
  }
  return null;
}

function runQuickQuery(q) { query = { ...q }; save(); renderQuery(); run(); }

// ------------------------------------------------------------------ run + results

function run() {
  let pq;
  try { pq = buildQuery(query); } catch (e) { showResult({ status: 'error', message: e.message }); return; }
  const t0 = performance.now();
  let r;
  try { r = prove(D, pq); } catch (e) { r = { status: 'error', message: `Internal error: ${e.message}` }; console.error(e); }
  r.ms = Math.round(performance.now() - t0);
  lastResult = r;
  showResult(r);
  if (r.status === 'proved' && r.lean && $('autoLean').checked && server.ok) checkLean();
}

const STATUS = { proved: ['proved', '✓ Proved'], refuted: ['refuted', '✗ False in general'], unknown: ['unknown', '? Undecided'], error: ['error', '! Cannot run'] };

function showResult(r) {
  $('resultPanel').hidden = false;
  const box = $('result');
  const [cls, label] = STATUS[r.status] || STATUS.error;
  let html = `<div class="row"><span class="status ${cls}">${label}</span>${r.ms !== undefined ? `<span class="small muted">chase: ${r.ms} ms</span>` : ''}</div>`;
  if (r.title) html += `<div class="claim">${mathHTML(r.title)}</div>`;
  if (r.message) html += `<p class="msg">${mathHTML(r.message)}</p>`;
  for (const b of r.blocks || []) {
    html += `<div class="proof-block"><h4 class="math">${mathHTML(b.title)}</h4><ul>`;
    for (const l of b.lines) {
      const indent = /^\s{2}/.test(l);
      const m = /^(.*?)\s{2,}(\(\d+\)(?:,\s*\(\d+\))*)$/.exec(l.trim());
      const body = m ? m[1] : l.trim();
      const tag = m ? `<span class="tag">${m[2]}</span>` : '';
      html += `<li class="${indent ? 'indent' : ''}"><span>${mathHTML(body)}</span>${tag}</li>`;
    }
    html += '</ul></div>';
  }
  if (r.counterexample) html += renderCx(r.counterexample);
  if (r.lean) {
    html += `<div class="lean-actions">
      <button id="copyLean">Copy Lean</button>
      <button id="dlLean">Download .lean</button>
      <button id="webLean" title="Open in the Lean 4 web editor (live.lean-lang.org, loads Mathlib)">Open in Lean 4 Web</button>
      ${server.ok ? '<button id="checkLean">Check with local Lean</button>' : ''}
    </div>
    <div id="leanStatus" class="lean-status">${leanHint()}</div>
    <details class="lean"><summary>Lean 4 + Mathlib proof (${r.lean.split('\n').length} lines)</summary><pre class="code">${esc(r.lean)}</pre></details>`;
  }
  box.innerHTML = html;
  if (r.lean) {
    $('copyLean').onclick = async () => { try { await navigator.clipboard.writeText(r.lean); $('copyLean').textContent = 'Copied'; } catch { $('copyLean').textContent = 'Copy failed'; } };
    $('dlLean').onclick = () => download('DiagramChase.lean', r.lean, 'text/plain');
    $('webLean').onclick = () => window.open(`https://live.lean-lang.org/#code=${encodeURIComponent(r.lean)}`, '_blank', 'noopener');
    if (server.ok) $('checkLean').onclick = checkLean;
    const rl = box.querySelector('a[href="#runLocally"]');
    if (rl) rl.onclick = (e) => { e.preventDefault(); showRunLocally(); };
  }
  $('resultPanel').scrollIntoView({ block: 'nearest', behavior: 'smooth' });
}

/** how to verify a proof when there is no local Lean checking */
function leanHint() {
  if (server.ok) return '';
  const local = `<a href="${RUN_LOCALLY}">run it locally</a>`;
  if (server.mode === 'nolean') {
    return `<span class="muted">server.py found no Lean + Mathlib project, so local checking is off. Restart it with <code>--lean-project PATH</code> (see ${local}), or use Lean 4 Web.</span>`;
  }
  return `<span class="muted">To verify, open the proof in Lean 4 Web: it loads the latest Mathlib, and the first check can take a minute or two. If it does not load or reports errors (very long proofs, a busy server, or a newer Mathlib), download the .lean file and check it with your own Lean + Mathlib, or ${local} with proof checking built in.</span>`;
}

function showRunLocally() {
  const p = $('helpPanel');
  p.hidden = false;
  $('helpBtn').setAttribute('aria-expanded', 'true');
  $('runLocally').scrollIntoView({ block: 'start', behavior: 'smooth' });
}

function renderCx(cx) {
  let html = '<div class="cx"><h4>Counterexample</h4><p class="small muted">Finite-dimensional ℚ-vector spaces (k[t]-modules with t acting as 0; tensor with k[t] for free ones). All hypotheses hold, the claim fails.</p>';
  html += `<table><tr>${cx.dims.map(d => `<th>${mathHTML(d.name)}</th>`).join('')}</tr><tr>${cx.dims.map(d => `<td>${d.dim === 0 ? '0' : `ℚ${d.dim > 1 ? `<sup>${d.dim}</sup>` : ''}`}</td>`).join('')}</tr></table>`;
  const mats = cx.matrices.filter(m => m.rows && m.cols);
  if (mats.length) {
    html += '<div class="matrices">';
    for (const m of mats) {
      html += `<span class="matrix"><span>${mathHTML(m.name)} =</span><span class="brk" style="grid-template-columns:repeat(${m.cols},auto)">${m.M.flat().map(x => `<span>${x}</span>`).join('')}</span></span>`;
    }
    html += '</div><p class="small muted">Maps between nonzero spaces shown as matrices (columns = basis of the source); all other maps are 0.</p>';
  }
  if (cx.witness && cx.witness.coords.length) html += `<p class="small">Witness in <span class="math">${mathHTML(cx.witness.module)}</span>: (${cx.witness.coords.join(', ')}).</p>`;
  return html + '</div>';
}

async function checkLean() {
  const r = lastResult;
  if (!r || !r.lean) return;
  const st = $('leanStatus');
  const btn = $('checkLean');
  if (btn) btn.disabled = true;
  st.className = 'lean-status';
  st.innerHTML = '<span class="spinner"></span> Checking with Lean + Mathlib… (loading Mathlib takes a while)';
  try {
    const res = await fetch('api/lean', { method: 'POST', headers: { 'Content-Type': 'application/json' }, body: JSON.stringify({ code: r.lean }) });
    const j = await res.json();
    if (lastResult !== r) return;
    if (j.ok) { st.className = 'lean-status ok'; st.textContent = `✓ Lean accepted the proof (${j.seconds}s).`; }
    else { st.className = 'lean-status fail'; st.innerHTML = `✗ Lean reported errors:<pre class="code">${esc(j.output || j.error || '')}</pre>`; }
  } catch (e) {
    st.className = 'lean-status fail'; st.textContent = `Could not reach the Lean server: ${e.message}`;
  } finally { if (btn) btn.disabled = false; }
}

function download(name, text, type) {
  const url = URL.createObjectURL(new Blob([text], { type }));
  const a = document.createElement('a');
  a.href = url; a.download = name; a.click();
  setTimeout(() => URL.revokeObjectURL(url), 1000);
}

// ------------------------------------------------------------------ examples, file io

function queryFormFrom(q) {
  const key = (p) => (p.length === 1 ? `a:${p[0]}` : `p:${p.join(',')}`);
  switch (q.type) {
    case 'injective': case 'surjective': case 'iso': case 'zero': return { type: q.type, map1: key(q.path) };
    case 'exact': return { type: 'exact', map1: key(q.first), map2: key(q.second) };
    case 'subset': case 'equal': {
      const f = { type: q.type };
      for (const s of ['lhs', 'rhs']) {
        f[`${s}Kind`] = q[s].kind;
        if (q[s].path) f[`${s}Map`] = key(q[s].path); else f[`${s}Module`] = q[s].module;
      }
      return f;
    }
    case 'existsMap': return { ...q };
    case 'induced': return { type: 'induced', arrow: q.arrow };
    default: return { type: 'injective' };
  }
}

function loadExample(id) {
  const ex = exampleById(id);
  if (!ex) return;
  snapshot();
  const { diagram, queries } = ex.make();
  D = diagram;
  sel = { m: new Set(), a: new Set() };
  query = queries.length ? queryFormFrom(queries[0]) : { type: 'injective' };
  $('resultPanel').hidden = true;
  changed();
  wrap.scrollTo(0, 0);
}

function init() {
  const sel0 = $('exampleSelect');
  for (const ex of EXAMPLES) {
    const o = document.createElement('option');
    o.value = ex.id; o.textContent = ex.title; o.title = ex.blurb;
    sel0.append(o);
  }
  sel0.onchange = () => { if (sel0.value) loadExample(sel0.value); sel0.value = ''; };
  $('newBtn').onclick = () => mutate(() => { D = M.emptyDiagram(); query = { type: 'injective' }; $('resultPanel').hidden = true; });
  $('exportBtn').onclick = () => download('diagram.json', JSON.stringify({ diagram: D, query }, null, 2), 'application/json');
  $('importInput').onchange = async (e) => {
    const f = e.target.files[0];
    if (!f) return;
    try {
      const j = JSON.parse(await f.text());
      const d = j.diagram || j;
      if (!Array.isArray(d.modules) || !Array.isArray(d.arrows)) throw new Error('not a diagram file');
      snapshot();
      D = { exact: [], squares: [], ...d };
      if (j.query) query = j.query;
      changed();
    } catch (err) { alert(`Could not open the file: ${err.message}`); }
    e.target.value = '';
  };
  $('undoBtn').onclick = undo;
  $('redoBtn').onclick = redo;
  $('modeSelect').onclick = () => setMode('select');
  $('modeArrow').onclick = () => setMode('arrow');
  $('helpBtn').onclick = () => {
    const p = $('helpPanel');
    p.hidden = !p.hidden;
    $('helpBtn').setAttribute('aria-expanded', String(!p.hidden));
  };
  $('runBtn').onclick = run;
  $('autoLean').onchange = save;
  const s = load();
  if (s) {
    D = s.diagram; query = s.query || query;
    $('autoLean').checked = s.autoLean !== false;
  } else {
    const { diagram, queries } = exampleById('five').make();
    D = diagram; query = queryFormFrom(queries[0]);
    $('autoLean').checked = true;
  }
  changed();
  window.addEventListener('resize', render);
  fetch('api/status').then(r => r.json()).then(j => {
    server = { ok: !!j.lean, mode: j.lean ? 'lean' : 'nolean', ...j };
    const cb = $('autoLean');
    if (!server.ok) { cb.checked = false; cb.disabled = true; cb.parentElement.title = j.message || 'Lean is not available'; }
    if (lastResult) showResult(lastResult);
  }).catch(() => {
    // static hosting (e.g. GitHub Pages): no local Lean checking at all
    server = { ok: false, mode: 'static' };
    const cb = $('autoLean');
    cb.checked = false;
    cb.parentElement.hidden = true;
    document.body.classList.add('static-site');
    if (lastResult) showResult(lastResult);
  });
}

init();
