// Diagram model: validation, Lean-safe names, path enumeration and the
// commutativity congruence (normal forms of paths + rewrite rules).

const LEAN_KEYWORDS = new Set(['fun', 'λ', 'let', 'have', 'show', 'from', 'in', 'at', 'by', 'do', 'then',
  'else', 'if', 'match', 'with', 'end', 'open', 'import', 'theorem', 'lemma', 'def', 'example', 'where',
  'structure', 'class', 'instance', 'variable', 'universe', 'section', 'namespace', 'Type', 'Prop', 'Sort',
  'calc', 'mut', 'return', 'for', 'unless', 'try', 'catch', 'finally', 'Π', 'Σ', 'forall', 'exists',
  'suffices', 'obtain', 'this', 'rfl', 'sorry', 'at', 'deriving', 'mutual', 'private', 'protected', 'noncomputable', 'partial', 'unsafe', 'macro', 'syntax', 'notation', 'infix', 'set_option', 'attribute', 'local', 'scoped', 'omit', 'include', 'using', 'renaming', 'hiding', 'exact', 'intro', 'rintro', 'refine', 'constructor', 'apply', 'simp', 'rw', 'ring', 'abel', 'decide', 'show', 'fun']);

export function leanIdent(name) {
  const clean = String(name).replace(/[«»]/g, '');
  if (/^[A-Za-zα-ωΑ-Ω][A-Za-z0-9_'α-ωΑ-Ω₀-₉]*$/.test(clean) && !/[λΠΣ]/.test(clean) && !LEAN_KEYWORDS.has(clean)) {
    return clean;
  }
  return `«${clean}»`;
}

export function displayName(obj) {
  return obj.kind === 'zero' ? '0' : obj.name;
}

/**
 * Validate and compile the editable diagram into index-based structures.
 * Throws an Error with a readable message on malformed diagrams.
 */
export function compile(diagram) {
  const errors = [];
  const objs = [];
  const objIndex = new Map();
  const usedLean = new Set(['𝕜', 'DC']);
  let zeroCount = 0;
  // modules joined by "=" (identity maps) are one module: they share a Lean type
  const ids = new Set(diagram.modules.map(m => m.id));
  const up = new Map(diagram.modules.map(m => [m.id, m.id]));
  const root = (x) => { while (up.get(x) !== x) x = up.get(x); return x; };
  for (const a of diagram.arrows) {
    if (a.equal && ids.has(a.src) && ids.has(a.dst)) up.set(root(a.src), root(a.dst));
  }
  const classOf = new Map(); // root -> {lean, kind, name}
  for (const m of diagram.modules) {
    const name = m.kind === 'zero' ? '0' : m.name;
    const kind = m.kind || 'general';
    const r = root(m.id);
    let lean;
    const cls = classOf.get(r);
    if (cls) {
      lean = cls.lean;
      if (cls.kind !== kind) errors.push(`Modules identified by “=” must have the same kind (${cls.name} is ${cls.kind}, ${name} is ${kind}).`);
    } else {
      if (m.kind === 'zero') {
        zeroCount += 1;
        lean = zeroCount === 1 ? '«0»' : `«0_${zeroCount}»`;
      } else {
        lean = leanIdent(name);
      }
      if (usedLean.has(lean)) errors.push(`Duplicate module name “${name}” (modules with the same name must be identified by an “=” map).`);
      usedLean.add(lean);
      classOf.set(r, { lean, kind, name });
    }
    objIndex.set(m.id, objs.length);
    objs.push({ id: m.id, name, kind, lean, construct: m.construct || null, i: objs.length });
  }
  const arrows = [];
  const arrowIndex = new Map();
  for (const a of diagram.arrows) {
    if (!objIndex.has(a.src) || !objIndex.has(a.dst)) { errors.push(`Arrow ${a.name} has a missing endpoint.`); continue; }
    const lean = leanIdent(a.name);
    if (usedLean.has(lean)) errors.push(`Duplicate name “${a.name}” (names of maps and modules must be distinct).`);
    usedLean.add(lean);
    arrowIndex.set(a.id, arrows.length);
    arrows.push({
      id: a.id, name: a.name, lean, i: arrows.length,
      src: objIndex.get(a.src), dst: objIndex.get(a.dst),
      mono: !a.equal && !!a.mono, epi: !a.equal && !!a.epi, zero: !a.equal && !!a.zero, dashed: !!a.dashed,
      equal: !!a.equal, auto: a.auto || null,
    });
    if (a.equal && a.dashed) errors.push(`The identity map ${a.name} cannot be induced (dashed).`);
  }
  const exact = [];
  for (const e of diagram.exact || []) {
    const i = arrowIndex.get(e.first), j = arrowIndex.get(e.second);
    if (i === undefined || j === undefined) continue;
    if (arrows[i].dst !== arrows[j].src) { errors.push(`Exact pair ${arrows[i].name}, ${arrows[j].name} is not composable.`); continue; }
    if (arrows[i].dashed || arrows[j].dashed) { errors.push(`Exactness cannot be assumed for the induced (dashed) map in ${arrows[i].name}, ${arrows[j].name}; ask it as a query instead.`); continue; }
    exact.push({ id: e.id, first: i, second: j, auto: e.auto || null });
  }
  const squares = [];
  for (const s of diagram.squares || []) {
    const q = { id: s.id, type: s.type, a1: arrowIndex.get(s.a1), a2: arrowIndex.get(s.a2), b1: arrowIndex.get(s.b1), b2: arrowIndex.get(s.b2) };
    if ([q.a1, q.a2, q.b1, q.b2].some(x => x === undefined)) continue;
    const [A1, A2, B1, B2] = [arrows[q.a1], arrows[q.a2], arrows[q.b1], arrows[q.b2]];
    if (A1.src !== A2.src || A1.dst !== B1.src || A2.dst !== B2.src || B1.dst !== B2.dst) {
      errors.push(`Square ${A1.name}, ${A2.name}, ${B1.name}, ${B2.name} is not well formed.`); continue;
    }
    if ([A1, A2, B1, B2].some(a => a.dashed)) { errors.push('Pullback/pushout squares cannot contain induced (dashed) maps.'); continue; }
    squares.push(q);
  }
  for (const a of arrows) {
    if (a.src === a.dst) errors.push(`Loop ${a.name} on ${objs[a.src].name}: endomorphisms are not supported by the chase engine.`);
  }
  // cycle check
  const color = new Array(objs.length).fill(0);
  const out = objs.map(() => []);
  for (const a of arrows) out[a.src].push(a);
  let cyclic = false;
  const dfs = (v) => {
    color[v] = 1;
    for (const a of out[v]) {
      if (color[a.dst] === 1) cyclic = true;
      else if (color[a.dst] === 0) dfs(a.dst);
    }
    color[v] = 2;
  };
  for (let v = 0; v < objs.length; v++) if (!color[v]) dfs(v);
  if (cyclic) {
    errors.push('The diagram has a directed cycle; the chase engine needs an acyclic diagram.'
      + (arrows.some(a => a.equal) ? ' The direction of an “=” map does not matter: reversing one may break the cycle.' : ''));
  }
  return { objs, arrows, exact, squares, errors, objIndex, arrowIndex, usedLean };
}

// ---------------------------------------------------------------- paths

export const pathKey = (arr) => arr.join(',');
export const parseKey = (k) => (k === '' ? [] : k.split(',').map(Number));

function arrowWeight(a) { return a.dashed ? 1000 : 1; }

/** comparison: (weight, length, lexicographic) — compatible with concatenation */
export function comparePaths(D, p, q) {
  const w = (arr) => arr.reduce((s, i) => s + arrowWeight(D.arrows[i]), 0);
  const d = w(p) - w(q);
  if (d) return d;
  if (p.length !== q.length) return p.length - q.length;
  for (let i = 0; i < p.length; i++) if (p[i] !== q[i]) return p[i] - q[i];
  return 0;
}

function containsWord(hay, needle) {
  outer: for (let i = 0; i + needle.length <= hay.length; i++) {
    for (let j = 0; j < needle.length; j++) if (hay[i + j] !== needle[j]) continue outer;
    return i;
  }
  return -1;
}

/**
 * A "phase" fixes which arrows exist, which path equalities are known
 * (generators) and which words are known to be zero (zero generators).
 * It computes equivalence classes of paths, normal forms, and minimal
 * rewrite rules with explicit derivations (for the Lean proof).
 */
export class Phase {
  constructor(D, arrowSet, generators, zeroGens) {
    this.D = D;
    this.arrowSet = arrowSet; // Set of arrow indices
    this.generators = generators; // [{p:[..], q:[..], name}]
    this.zeroGens = zeroGens; // [{w:[..], name}]
    this.enumerate();
    this.close();
  }

  enumerate() {
    const { D } = this;
    const out = D.objs.map(() => []);
    for (const i of this.arrowSet) out[D.arrows[i].src].push(i);
    this.out = out;
    this.paths = new Map(); // key -> {arr, src, dst}
    this.from = D.objs.map(() => []);
    this.to = D.objs.map(() => []);
    const walk = (src, v, arr) => {
      for (const i of out[v]) {
        const nxt = arr.concat([i]);
        const k = pathKey(nxt);
        const rec = { arr: nxt, src, dst: D.arrows[i].dst, key: k };
        this.paths.set(k, rec);
        this.from[src].push(rec);
        this.to[rec.dst].push(rec);
        walk(src, D.arrows[i].dst, nxt);
      }
    };
    for (let v = 0; v < D.objs.length; v++) walk(v, v, []);
  }

  find(k) {
    let r = k;
    while (this.parent.get(r) !== r) r = this.parent.get(r);
    let c = k;
    while (this.parent.get(c) !== r) { const n = this.parent.get(c); this.parent.set(c, r); c = n; }
    return r;
  }

  union(a, b) {
    const ra = this.find(a), rb = this.find(b);
    if (ra === rb) return false;
    this.parent.set(ra, rb);
    this.zeroFlag.set(rb, this.zeroFlag.get(rb) || this.zeroFlag.get(ra));
    return true;
  }

  addGeneratorClosure(p, q) {
    const src = this.D.arrows[p[0]].src;
    const dst = this.D.arrows[p[p.length - 1]].dst;
    const pres = [[]].concat(this.to[src].map(r => r.arr));
    const sufs = [[]].concat(this.from[dst].map(r => r.arr));
    for (const r of pres) for (const s of sufs) {
      const a = pathKey(r.concat(p, s)), b = pathKey(r.concat(q, s));
      if (this.paths.has(a) && this.paths.has(b)) this.union(a, b);
    }
  }

  initUF() {
    this.parent = new Map();
    this.zeroFlag = new Map();
    for (const [k, rec] of this.paths) {
      this.parent.set(k, k);
      this.zeroFlag.set(k, this.zeroGens.some(z => containsWord(rec.arr, z.w) >= 0));
    }
  }

  close() {
    this.initUF();
    for (const g of this.generators) this.addGeneratorClosure(g.p, g.q);
    // normal forms: least member of each class
    this.members = new Map();
    for (const k of this.paths.keys()) {
      const r = this.find(k);
      if (!this.members.has(r)) this.members.set(r, []);
      this.members.get(r).push(k);
    }
    this.nfOf = new Map();
    for (const [r, ks] of this.members) {
      const sorted = ks.map(k => this.paths.get(k).arr).sort((a, b) => comparePaths(this.D, a, b));
      this.nfOf.set(r, this.zeroFlag.get(r) ? null : pathKey(sorted[0]));
      this.members.set(r, sorted.map(pathKey));
    }
  }

  /** normal form key of a path key ('' = identity), or null if the path is zero */
  nf(k) {
    if (k === '') return '';
    if (!this.paths.has(k)) throw new Error(`unknown path ${k}`);
    return this.nfOf.get(this.find(k));
  }

  concat(k1, k2) {
    if (k1 === '') return k2;
    if (k2 === '') return k1;
    return `${k1},${k2}`;
  }

  srcOf(k, fallbackObj) { return k === '' ? fallbackObj : this.D.arrows[parseKey(k)[0]].src; }
  dstOf(k, fallbackObj) { const a = parseKey(k); return a.length ? this.D.arrows[a[a.length - 1]].dst : fallbackObj; }

  /** all normal nonzero path classes starting at obj (including the identity) */
  classesFrom(obj) {
    const seen = new Set(['']);
    const res = [{ key: '', dst: obj }];
    for (const rec of this.from[obj]) {
      const n = this.nf(rec.key);
      if (n === null || seen.has(n)) continue;
      seen.add(n);
      res.push({ key: n, dst: rec.dst });
    }
    return res;
  }

  /** normal nonzero classes of paths from src to dst (identity if equal) */
  classesBetween(src, dst) {
    return this.classesFrom(src).filter(c => c.dst === dst);
  }

  isNormal(k) { return this.nf(k) === k; }

  /** rewrite rules: minimal non-normal words, with derivations */
  rules() {
    if (this._rules) return this._rules;
    const rules = [];
    for (const [k, rec] of this.paths) {
      const n = this.nf(k);
      if (n === k) continue;
      const arr = rec.arr;
      let minimal = true;
      for (let len = 1; len < arr.length && minimal; len++) {
        for (let i = 0; i + len <= arr.length; i++) {
          if (!this.isNormal(pathKey(arr.slice(i, i + len)))) { minimal = false; break; }
        }
      }
      if (!minimal) continue;
      rules.push({ lhs: arr, rhs: n === null ? null : parseKey(n), proof: this.derive(arr, n) });
    }
    this._rules = rules;
    return rules;
  }

  /** BFS through generator applications from word to target (a key) or to a word containing a zero generator */
  derive(arr, target) {
    if (target === null) {
      const z = this.zeroGens.find(z => pathKey(z.w) === pathKey(arr));
      if (z) return { kind: 'zgen', zgen: z.name };
    }
    const start = pathKey(arr);
    const prev = new Map([[start, null]]);
    const queue = [start];
    const moves = [];
    for (const g of this.generators) {
      moves.push({ from: g.p, to: g.q, name: g.name, dir: 'fwd' });
      moves.push({ from: g.q, to: g.p, name: g.name, dir: 'bwd' });
    }
    let found = null, zhit = null;
    while (queue.length) {
      const cur = queue.shift();
      const w = parseKey(cur);
      if (target !== null && cur === target) { found = cur; break; }
      if (target === null) {
        const z = this.zeroGens.find(z => containsWord(w, z.w) >= 0);
        if (z) { found = cur; zhit = z; break; }
      }
      for (const m of moves) {
        const pos = containsWord(w, m.from);
        if (pos < 0) continue;
        const nw = w.slice(0, pos).concat(m.to, w.slice(pos + m.from.length));
        const nk = pathKey(nw);
        if (!this.paths.has(nk) || prev.has(nk)) continue;
        prev.set(nk, { from: cur, move: m });
        queue.push(nk);
      }
    }
    if (found === null) throw new Error(`internal: no derivation for ${start}`);
    const steps = [];
    for (let c = found; prev.get(c); c = prev.get(c).from) steps.push(prev.get(c).move);
    steps.reverse();
    return { kind: target === null ? 'zero' : 'eq', steps, zgen: zhit ? zhit.name : null };
  }
}

/** zero generators of the base diagram */
export function baseZeroGens(D, arrowSet) {
  const zs = [];
  D.exact.forEach((e, n) => {
    if (arrowSet.has(e.first) && arrowSet.has(e.second)) zs.push({ w: [e.first, e.second], name: null, source: { type: 'exact', index: n } });
  });
  for (const i of arrowSet) {
    const a = D.arrows[i];
    if (a.dashed) continue;
    if (a.zero) zs.push({ w: [i], name: null, source: { type: 'zeroMap', arrow: i } });
    else if (D.objs[a.dst].kind === 'zero') zs.push({ w: [i], name: null, source: { type: 'intoZero', arrow: i } });
    else if (D.objs[a.src].kind === 'zero') zs.push({ w: [i], name: null, source: { type: 'fromZero', arrow: i } });
  }
  return zs;
}

/**
 * Minimal generating set of commutativity relations for the solid
 * (non-dashed) part of the diagram: every two parallel paths are equal.
 */
export function baseGenerators(D, arrowSet, zeroGens) {
  const tmp = new Phase(D, arrowSet, [], zeroGens);
  const byEnds = new Map();
  for (const rec of tmp.paths.values()) {
    const k = `${rec.src}>${rec.dst}`;
    if (!byEnds.has(k)) byEnds.set(k, []);
    byEnds.get(k).push(rec.arr);
  }
  const cands = [];
  for (const list of byEnds.values()) {
    if (list.length < 2) continue;
    list.sort((a, b) => comparePaths(D, a, b));
    for (let i = 1; i < list.length; i++) cands.push({ p: list[i], q: list[0] });
  }
  cands.sort((x, y) => (x.p.length + x.q.length) - (y.p.length + y.q.length) || comparePaths(D, x.p, y.p));
  const gens = [];
  for (const c of cands) {
    const a = pathKey(c.p), b = pathKey(c.q);
    const ra = tmp.find(a), rb = tmp.find(b);
    if (ra === rb) continue;
    if (tmp.zeroFlag.get(ra) && tmp.zeroFlag.get(rb)) continue;
    gens.push({ p: c.p, q: c.q, name: null, source: { type: 'comm' } });
    tmp.addGeneratorClosure(c.p, c.q);
  }
  return gens;
}

/**
 * Commutativity constraints that an induced (dashed) arrow d must satisfy,
 * relative to the arrows in arrowSet (which must contain d). Only
 * "trimmed-minimal" constraints are returned: P_out ∘ d ∘ P_in = Q with Q
 * free of d.
 */
export function dashedConstraints(D, arrowSet, d) {
  const solid = new Set([...arrowSet].filter(i => i !== d));
  const ph = new Phase(D, solid, [], []);
  const hasFree = (u, v) => u === v ? false : ph.from[u].some(r => r.dst === v);
  const freePath = (u, v) => {
    const list = ph.from[u].filter(r => r.dst === v).map(r => r.arr).sort((a, b) => comparePaths(D, a, b));
    return list[0];
  };
  const X = D.arrows[d].src, Y = D.arrows[d].dst;
  const ins = [[]].concat(ph.to[X].map(r => r.arr));
  const outs = [[]].concat(ph.from[Y].map(r => r.arr));
  const res = [];
  for (const pin of ins) for (const pout of outs) {
    const U = pin.length ? D.arrows[pin[0]].src : X;
    const V = pout.length ? D.arrows[pout[pout.length - 1]].dst : Y;
    if (!hasFree(U, V)) continue;
    // minimality: no proper trimming with a d-free path
    let minimal = true;
    const inVerts = pin.map(i => D.arrows[i].src).concat([X]); // U ... X
    const outVerts = [Y].concat(pout.map(i => D.arrows[i].dst)); // Y ... V
    for (let a = 0; a < inVerts.length && minimal; a++) {
      for (let b = 0; b < outVerts.length; b++) {
        if (a === 0 && b === outVerts.length - 1) continue;
        if (hasFree(inVerts[a], outVerts[b])) { minimal = false; break; }
      }
    }
    if (!minimal) continue;
    res.push({ lhs: pin.concat([d], pout), rhs: freePath(U, V), src: U, dst: V });
  }
  return res;
}
