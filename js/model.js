// Editable diagram model shared by the UI, the examples and the tests.

let counter = 0;
export const uid = (p) => `${p}${Date.now().toString(36)}${(counter++).toString(36)}`;

export function emptyDiagram() {
  return { version: 1, modules: [], arrows: [], exact: [], squares: [] };
}

export function moduleById(d, id) { return d.modules.find(m => m.id === id); }
export function arrowById(d, id) { return d.arrows.find(a => a.id === id); }

export function nextModuleName(d) {
  const used = new Set(d.modules.map(m => m.name));
  for (const c of 'ABCDEFGHIJKLMNOPQRSTUVWYZ') if (!used.has(c)) return c;
  for (const c of 'ABCDEFGHIJKLMNOPQRSTUVWYZ') for (const s of ["'", "''"]) if (!used.has(c + s)) return c + s;
  return `M${d.modules.length}`;
}

export function nextArrowName(d) {
  const used = new Set(d.arrows.map(a => a.name));
  for (const c of 'fghjkuvwpqrsabcdlmn') if (!used.has(c)) return c;
  for (const c of 'fghjkuvw') for (const s of ["'", "''"]) if (!used.has(c + s)) return c + s;
  return `f${d.arrows.length}`;
}

/** default name of an identity map "=" out of a module: id_A, id_A', … */
export function nextIdName(d, src) {
  const m = moduleById(d, src);
  const base = `id_${m && m.kind !== 'zero' ? m.name : '0'}`;
  const used = new Set(d.arrows.map(a => a.name));
  if (!used.has(base)) return base;
  for (let n = 2; ; n++) if (!used.has(`${base}${n}`)) return `${base}${n}`;
}

/**
 * Modules identified with m by "=" (identity) maps, m included. They are one
 * and the same module; the "=" maps between them are identities.
 */
export function equalClass(d, id) {
  const cls = new Set([id]);
  const queue = [id];
  while (queue.length) {
    const v = queue.pop();
    for (const a of d.arrows) {
      if (!a.equal) continue;
      const w = a.src === v ? a.dst : a.dst === v ? a.src : null;
      if (w && !cls.has(w)) { cls.add(w); queue.push(w); }
    }
  }
  return [...cls].map(x => moduleById(d, x)).filter(Boolean);
}

/**
 * Make a map an identity "=" (on) or an ordinary map (off). An identity is not
 * a hypothesis on a map but an identification of modules: the target becomes
 * the same module as the source (same kind), and the map is id. It carries no
 * other properties and cannot be induced.
 */
export function setEqual(d, id, on) {
  const a = arrowById(d, id);
  if (!a || a.auto) return;
  if (on) {
    a.equal = true;
    a.mono = a.epi = a.zero = a.dashed = false;
    const S = moduleById(d, a.src);
    for (const m of equalClass(d, a.src)) if (!m.construct) m.kind = S.kind;
    if (!/^id_/.test(a.name)) renameArrow(d, id, nextIdName(d, a.src));
    // ker / im / coker of an identity are trivial: drop them
    const dead = d.modules.filter(m => m.construct && m.construct.arrow === id).map(m => m.id);
    if (dead.length) deleteItems(d, { modules: dead });
  } else {
    delete a.equal;
    if (/^id_/.test(a.name)) renameArrow(d, id, nextArrowName(d));
  }
}

/** reverse an "=" map (its direction carries no meaning); drops exactness/squares through it */
export function reverseEqual(d, id) {
  const a = arrowById(d, id);
  if (!a || !a.equal) return;
  [a.src, a.dst] = [a.dst, a.src];
  d.exact = d.exact.filter(e => e.first !== id && e.second !== id);
  d.squares = d.squares.filter(s => ![s.a1, s.a2, s.b1, s.b2].includes(id));
}

/** set the kind of a module and of every module identified with it by "=" */
export function setKind(d, id, kind) {
  for (const m of equalClass(d, id)) if (!m.construct) m.kind = kind;
}

export function cellFree(d, x, y) { return !d.modules.some(m => m.x === x && m.y === y); }

export function nearestFree(d, x, y) {
  if (cellFree(d, x, y)) return { x, y };
  for (let r = 1; r < 20; r++) {
    for (let dy = -r; dy <= r; dy++) for (let dx = -r; dx <= r; dx++) {
      if (Math.max(Math.abs(dx), Math.abs(dy)) !== r) continue;
      if (x + dx < 0 || y + dy < 0) continue;
      if (cellFree(d, x + dx, y + dy)) return { x: x + dx, y: y + dy };
    }
  }
  return { x, y };
}

export function addModule(d, { name, x, y, kind = 'general', construct = null, id = null }) {
  const m = { id: id || uid('m'), name: name || nextModuleName(d), kind, x, y };
  if (construct) m.construct = construct;
  d.modules.push(m);
  return m;
}

export function addArrow(d, { src, dst, name, mono = false, epi = false, zero = false, dashed = false, equal = false, auto = null, id = null, bend = 0 }) {
  const a = { id: id || uid('a'), name: name || (equal ? nextIdName(d, src) : nextArrowName(d)), src, dst, mono, epi, zero, dashed, bend };
  if (equal) a.equal = true;
  if (auto) a.auto = auto;
  d.arrows.push(a);
  return a;
}

export function addExact(d, first, second, auto = null) {
  if (d.exact.some(e => e.first === first && e.second === second)) return null;
  const e = { id: uid('e'), first, second };
  if (auto) e.auto = auto;
  d.exact.push(e);
  return e;
}

/** mark a composable chain of arrows exact at every inner object */
export function addExactChain(d, ids) {
  const res = [];
  for (let i = 0; i + 1 < ids.length; i++) res.push(addExact(d, ids[i], ids[i + 1]));
  return res;
}

/** order a set of arrow ids into a composable chain, or null */
export function chainOrder(d, ids) {
  const arrows = ids.map(id => arrowById(d, id));
  const starts = arrows.filter(a => !arrows.some(b => b.dst === a.src));
  if (starts.length !== 1) return null;
  const out = [starts[0]];
  while (out.length < arrows.length) {
    const last = out[out.length - 1];
    const nxt = arrows.filter(a => a.src === last.dst && !out.includes(a));
    if (nxt.length !== 1) return null;
    out.push(nxt[0]);
  }
  return out.map(a => a.id);
}

/** recognise four arrows forming a square; returns {a1, a2, b1, b2} (a's out of the source corner) */
export function squareShape(d, ids) {
  if (ids.length !== 4) return null;
  const arrows = ids.map(id => arrowById(d, id));
  for (const a1 of arrows) for (const a2 of arrows) {
    if (a1 === a2 || a1.src !== a2.src) continue;
    const rest = arrows.filter(a => a !== a1 && a !== a2);
    for (const [b1, b2] of [[rest[0], rest[1]], [rest[1], rest[0]]]) {
      if (b1.src === a1.dst && b2.src === a2.dst && b1.dst === b2.dst) {
        const [x1, x2] = a1.id < a2.id ? [a1, a2] : [a1, a2];
        return { a1: x1.id, a2: x2.id, b1: b1.id, b2: b2.id };
      }
    }
  }
  return null;
}

export function addSquare(d, type, shape) {
  const s = { id: uid('s'), type, ...shape };
  d.squares.push(s);
  return s;
}

const CON_LABEL = { ker: 'ker', im: 'im', coker: 'coker' };
/** a map name as it appears inside other names: composites get parentheses */
const fnLabel = (name) => (name.includes('∘') ? `(${name})` : name);

/** add ker / im / coker of an arrow together with its universal maps */
export function addConstruction(d, type, arrowId) {
  const f = arrowById(d, arrowId);
  if (!f) return null;
  const existing = d.modules.find(m => m.construct && m.construct.type === type && m.construct.arrow === arrowId);
  if (existing) return existing;
  const A = moduleById(d, f.src), B = moduleById(d, f.dst);
  const fn = fnLabel(f.name);
  const name = `${CON_LABEL[type]} ${fn}`;
  let pos;
  // constructions above the diagram's top row: make room by shifting everything down
  if ((type === 'ker' && A.y === 0) || (type === 'im' && Math.min(A.y, B.y) === 0)) {
    for (const m of d.modules) m.y += 1;
  }
  if (type === 'ker') pos = nearestFree(d, A.x, Math.max(0, A.y - 1));
  else if (type === 'coker') pos = nearestFree(d, B.x, B.y + 1);
  else pos = nearestFree(d, Math.round((A.x + B.x) / 2), Math.max(0, Math.min(A.y, B.y) - 1));
  const M = addModule(d, { name, x: pos.x, y: pos.y, construct: { type, arrow: arrowId } });
  const auto = { type, of: arrowId };
  if (type === 'ker') {
    const i = addArrow(d, { src: M.id, dst: A.id, name: `ι_${fn}`, mono: true, auto });
    addExact(d, i.id, f.id, auto);
  } else if (type === 'coker') {
    const p = addArrow(d, { src: B.id, dst: M.id, name: `π_${fn}`, epi: true, auto });
    addExact(d, f.id, p.id, auto);
  } else {
    addArrow(d, { src: A.id, dst: M.id, name: `e_${fn}`, epi: true, auto });
    addArrow(d, { src: M.id, dst: B.id, name: `m_${fn}`, mono: true, auto });
  }
  return M;
}

/** default name of the composite of a chain (first map first): "g∘f" */
export function compositeName(d, ids) {
  return ids.slice().reverse().map(id => arrowById(d, id).name).join('∘');
}

/**
 * Add a map equal to the composite of a composable chain of maps. Commutativity
 * of the diagram makes it equal to the composite; it is dashed (induced) when
 * one of the factors is.
 */
export function addComposite(d, ids) {
  const chain = chainOrder(d, ids);
  if (!chain || chain.length < 2) return null;
  const first = arrowById(d, chain[0]), last = arrowById(d, chain[chain.length - 1]);
  if (first.src === last.dst) return null;
  const existing = d.arrows.find(a => a.composite && a.composite.join(',') === chain.join(','));
  if (existing) return existing;
  const A = moduleById(d, first.src), B = moduleById(d, last.dst);
  // curve the new map if it would run straight through another module or along another map
  const blocked = d.modules.some(m => m !== A && m !== B && onSegment(A, B, m));
  const parallel = d.arrows.filter(a => (a.src === A.id && a.dst === B.id) || (a.src === B.id && a.dst === A.id)).length;
  // labels sit on the left of a map, so curve to the right (e.g. below a row) first
  let bend = 0;
  if (blocked || parallel) bend = parallel % 2 ? Math.ceil((parallel + 1) / 2) : -Math.ceil((parallel + 1) / 2);
  const a = addArrow(d, {
    src: A.id, dst: B.id, name: compositeName(d, chain),
    dashed: chain.some(id => arrowById(d, id).dashed), bend,
  });
  a.composite = chain;
  return a;
}

function onSegment(A, B, m) {
  const dx = B.x - A.x, dy = B.y - A.y;
  const len2 = dx * dx + dy * dy;
  const t = ((m.x - A.x) * dx + (m.y - A.y) * dy) / len2;
  if (t <= 0 || t >= 1) return false;
  const px = A.x + t * dx - m.x, py = A.y + t * dy - m.y;
  return Math.hypot(px, py) < 0.3;
}

/** delete modules/arrows with cascading cleanup (constructions of deleted arrows vanish too) */
export function deleteItems(d, { modules = [], arrows = [] }) {
  const delM = new Set(modules), delA = new Set(arrows);
  let changed = true;
  while (changed) {
    changed = false;
    for (const a of d.arrows) {
      if (!delA.has(a.id) && (delM.has(a.src) || delM.has(a.dst))) { delA.add(a.id); changed = true; }
    }
    for (const m of d.modules) {
      if (!delM.has(m.id) && m.construct && delA.has(m.construct.arrow)) { delM.add(m.id); changed = true; }
    }
    for (const a of d.arrows) {
      if (!delA.has(a.id) && a.composite && a.composite.some(id => delA.has(id))) { delA.add(a.id); changed = true; }
    }
  }
  d.modules = d.modules.filter(m => !delM.has(m.id));
  d.arrows = d.arrows.filter(a => !delA.has(a.id));
  d.exact = d.exact.filter(e => !delA.has(e.first) && !delA.has(e.second));
  d.squares = d.squares.filter(s => ![s.a1, s.a2, s.b1, s.b2].some(id => delA.has(id)));
}

/** rename an arrow and keep the names of its constructions in sync */
export function renameArrow(d, id, name) {
  const a = arrowById(d, id);
  if (!a) return;
  const old = a.name;
  // composites that still carry their default name follow the rename
  const defaults = d.arrows.filter(b => b.composite && b.composite.includes(id) && b.name === compositeName(d, b.composite));
  a.name = name;
  for (const b of defaults) renameArrow(d, b.id, compositeName(d, b.composite));
  for (const m of d.modules) {
    if (m.construct && m.construct.arrow === id) m.name = `${CON_LABEL[m.construct.type]} ${fnLabel(name)}`;
  }
  const oldL = fnLabel(old);
  for (const b of d.arrows) {
    if (b.auto && b.auto.of === id && b.name.endsWith(`_${oldL}`)) b.name = b.name.slice(0, -oldL.length) + fnLabel(name);
  }
}
