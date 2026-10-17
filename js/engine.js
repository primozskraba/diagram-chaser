// Element-level diagram chase engine.
//
// State: element variables x living in modules; an element of module B is a
// Q-linear combination of atoms (x, p) = p(x) where p is a normal path from
// the module of x to B. For every module B we keep the subspace K_B of
// combinations known to be zero, together with certificates (how each known
// relation is a combination of pushed-forward facts). Rules:
//   deterministic: injective maps, zero modules, pullback separation;
//   existential:   exactness lifts, surjective lifts, pullback lifts,
//                  pushout covers and relations (these introduce new variables).
// If the rules saturate without reaching the goal, the quotients E_B / K_B
// form a finite-dimensional counterexample.

import { Q, ONE, MINUS_ONE } from './rational.js';
import { TrackedBasis, addTo, axpy, scale } from './linalg.js';
import { parseKey } from './diagram.js';

const SUB = '₀₁₂₃₄₅₆₇₈₉';
export const subscript = (n) => String(n).split('').map(d => SUB[+d]).join('');

export class Chase {
  /**
   * hyps: {
   *   mono: [{arrow, ref}], epi: [{arrow, ref}], exact: [{first, second, ref}],
   *   pb: [{sq, ref}], po: [{sq, ref}],
   *   zigzag: [{arrow, X, Y, steps: [{arrow, dir}], objs: [v0..vn], tot, def}]
   * }
   * A zigzag hypothesis says the (dashed) arrow is the map whose graph is the
   * relation obtained by walking the steps (forward along a map, or backward =
   * taking preimages); its unfolding rule introduces the intermediate elements.
   */
  constructor(D, phase, hyps, opts = {}) {
    this.D = D;
    this.phase = phase;
    this.hyps = hyps;
    this.opts = { maxRounds: 10, maxVars: 60, ...opts };
    this.fresh = opts.fresh; // function(base) -> unique Lean-safe name
    this.vars = [];
    this.atoms = new Map();
    this.atomsAt = D.objs.map(() => []);
    this.facts = [];
    this.K = D.objs.map(() => new TrackedBasis(k => this.atoms.get(k).idx));
    this.steps = [];
    this.unfolded = new Set();
  }

  // ------------------------------------------------------------ variables

  newVar(obj, human, step) {
    const o = this.D.objs[obj];
    let base = 'x';
    const first = o.name.replace(/[^A-Za-z]/g, '')[0];
    if (o.construct) base = { ker: 'k', im: 'i', coker: 'c' }[o.construct.type] || 'x';
    else if (first) base = first.toLowerCase();
    const name = this.fresh(base);
    const v = { id: this.vars.length, name, obj, step, human: human || name };
    this.vars.push(v);
    for (const c of this.phase.classesFrom(obj)) this.atom(v.id, c.key, c.dst);
    return v;
  }

  atom(varId, path, dst) {
    const key = `${varId}|${path}`;
    if (!this.atoms.has(key)) {
      const a = { key, idx: this.atoms.size, varId, path, obj: dst };
      this.atoms.set(key, a);
      this.atomsAt[dst].push(key);
    }
    return key;
  }

  varVec(v) { return new Map([[`${v.id}|`, ONE]]); }

  /** push a vector along a path (key); returns a vector in the target module */
  push(vec, pk) {
    const out = new Map();
    if (pk === '') return new Map(vec);
    for (const [k, c] of vec) {
      const a = this.atoms.get(k);
      const n = this.phase.nf(this.phase.concat(a.path, pk));
      if (n === null) continue;
      const dst = this.phase.dstOf(n, this.vars[a.varId].obj);
      addTo(out, this.atom(a.varId, n, dst), c);
    }
    return out;
  }

  vecObj(vec, fallback) {
    for (const k of vec.keys()) return this.atoms.get(k).obj;
    return fallback;
  }

  // ------------------------------------------------------------ facts

  addFact(obj, vec, info) {
    const f = { id: this.facts.length, obj, vec, ...info };
    this.facts.push(f);
    for (const c of this.phase.classesFrom(obj)) {
      const pv = this.push(vec, c.key);
      if (pv.size === 0) continue;
      this.K[c.dst].insert(pv, new Map([[`F${f.id}#${c.key}`, ONE]]));
    }
    return f;
  }

  inK(obj, vec) { return this.K[obj].express(vec); }

  /** a basis over several target modules; keys are prefixed with the component index */
  space(objs) {
    const tb = new TrackedBasis(k => {
      const bar = k.indexOf('|');
      return this.atoms.get(k.slice(bar + 1)).idx * 8 + Number(k.slice(0, bar));
    });
    objs.forEach((obj, i) => {
      for (const row of this.K[obj].rows.values()) {
        tb.insert(prefix(row.vec, i), prefix(row.tag, i));
      }
    });
    return tb;
  }

  /**
   * Kernel of a linear map from a domain (given by the images of domain keys,
   * in prefixed target keys) to the quotient of targets by the K's.
   * Returns [{lam: Map domainKey->Q, cert: Map prefixedTag->Q}] where
   * image(lam) = sum cert * (pushed facts).
   */
  kernel(domain, targets) {
    const tb = this.space(targets);
    const res = [];
    for (const { key, img } of domain) {
      const r = tb.insert(img, new Map([[`L:${key}`, ONE]]));
      if (r.vec.size) continue;
      const lam = new Map(), cert = new Map();
      for (const [k, c] of r.tag) {
        if (k.startsWith('L:')) lam.set(k.slice(2), c);
        else cert.set(k, c.neg());
      }
      res.push({ lam, cert });
    }
    return res;
  }

  /** v (in obj) ∈ φ(E_src) + K_obj ? returns {t, cert} with φ(t) - v = sum cert*facts */
  solveImage(v, obj, src, pk) {
    const tb = this.space([obj]);
    for (const a of this.atomsAt[src]) {
      tb.insert(prefix(this.push(new Map([[a, ONE]]), pk), 0), new Map([[`L:${a}`, ONE]]));
    }
    const S = tb.express(prefix(v, 0));
    if (!S) return null;
    const t = new Map(), cert = new Map();
    for (const [k, c] of S) {
      if (k.startsWith('L:')) t.set(k.slice(2), c);
      else cert.set(k, c.neg());
    }
    return { t, cert: unprefix(cert) };
  }

  // ------------------------------------------------------------ deterministic rules

  saturate() {
    let changed = true, total = 0;
    while (changed) {
      changed = false;
      for (const h of this.hyps.mono) {
        const a = this.D.arrows[h.arrow];
        const pk = String(h.arrow);
        const dom = this.atomsAt[a.src].map(k => ({ key: k, img: prefix(this.push(new Map([[k, ONE]]), pk), 0) }));
        for (const { lam, cert } of this.kernel(dom, [a.dst])) {
          if (this.inK(a.src, lam)) continue;
          const f = this.addFact(a.src, lam, { how: 'inj' });
          this.steps.push({ kind: 'inj', hyp: h, arrow: h.arrow, v: lam, cert: unprefix(cert), fact: f });
          f.step = this.steps.length - 1;
          changed = true; total++;
        }
      }
      for (let o = 0; o < this.D.objs.length; o++) {
        if (this.D.objs[o].kind !== 'zero') continue;
        for (const k of this.atomsAt[o]) {
          const v = new Map([[k, ONE]]);
          if (this.inK(o, v)) continue;
          const f = this.addFact(o, v, { how: 'zeroObj' });
          this.steps.push({ kind: 'zeroObj', obj: o, v, fact: f });
          f.step = this.steps.length - 1;
          changed = true; total++;
        }
      }
      for (const h of this.hyps.pb) {
        const s = h.sq, A = this.D.arrows;
        const P = A[s.a1].src, X1 = A[s.a1].dst, X2 = A[s.a2].dst;
        const dom = this.atomsAt[P].map(k => {
          const e = new Map([[k, ONE]]);
          const img = prefix(this.push(e, String(s.a1)), 0);
          for (const [kk, c] of prefix(this.push(e, String(s.a2)), 1)) img.set(kk, c);
          return { key: k, img };
        });
        for (const { lam, cert } of this.kernel(dom, [X1, X2])) {
          if (this.inK(P, lam)) continue;
          const f = this.addFact(P, lam, { how: 'pbSep' });
          this.steps.push({ kind: 'pbSep', hyp: h, v: lam, cert1: unprefix(cert, 0), cert2: unprefix(cert, 1), fact: f });
          f.step = this.steps.length - 1;
          changed = true; total++;
        }
      }
    }
    return total;
  }

  // ------------------------------------------------------------ existential rules

  existentialRound() {
    let added = 0;
    this.truncated = false;
    const room = () => {
      if (this.vars.length < this.opts.maxVars) return true;
      this.truncated = true;
      return false;
    };
    const A = this.D.arrows;
    // exactness lifts
    const exactPlans = [];
    for (const h of this.hyps.exact) {
      const psi = A[h.first], phi = A[h.second];
      const B = psi.dst;
      const dom = this.atomsAt[B].map(k => ({ key: k, img: prefix(this.push(new Map([[k, ONE]]), String(h.second)), 0) }));
      const ker = this.kernel(dom, [phi.dst]);
      if (!ker.length) continue;
      const tb = this.space([B]);
      for (const a of this.atomsAt[psi.src]) tb.insert(prefix(this.push(new Map([[a, ONE]]), String(h.first)), 0), new Map());
      for (const { lam, cert } of ker) {
        const r = tb.insert(prefix(lam, 0), new Map());
        if (r.vec.size === 0) continue;
        exactPlans.push({ h, v: lam, cert: unprefix(cert) });
      }
    }
    for (const p of exactPlans) {
      if (!room()) break;
      const psi = A[p.h.first];
      const step = { kind: 'exactLift', hyp: p.h, v: p.v, cert: p.cert };
      this.steps.push(step);
      const x = this.newVar(psi.src, null, this.steps.length - 1);
      const vec = axpy(this.push(this.varVec(x), String(p.h.first)), MINUS_ONE, p.v);
      step.newVar = x;
      step.fact = this.addFact(psi.dst, vec, { how: 'exactLift', step: this.steps.length - 1 });
      added++;
    }
    // surjective lifts
    for (const h of this.hyps.epi) {
      const phi = A[h.arrow];
      const tb = this.space([phi.dst]);
      for (const a of this.atomsAt[phi.src]) tb.insert(prefix(this.push(new Map([[a, ONE]]), String(h.arrow)), 0), new Map());
      for (const k of [...this.atomsAt[phi.dst]]) {
        if (!room()) break;
        const v = new Map([[k, ONE]]);
        const r = tb.insert(prefix(v, 0), new Map());
        if (r.vec.size === 0) continue;
        const step = { kind: 'epiLift', hyp: h, v };
        this.steps.push(step);
        const x = this.newVar(phi.src, null, this.steps.length - 1);
        step.newVar = x;
        step.fact = this.addFact(phi.dst, axpy(this.push(this.varVec(x), String(h.arrow)), MINUS_ONE, v), { how: 'epiLift', step: this.steps.length - 1 });
        added++;
      }
    }
    // pullback lifts: pairs (u,w) with b1 u - b2 w = 0
    for (const h of this.hyps.pb) {
      const s = h.sq;
      const P = A[s.a1].src, X1 = A[s.a1].dst, X2 = A[s.a2].dst, T = A[s.b1].dst;
      const dom = [
        ...this.atomsAt[X1].map(k => ({ key: `1|${k}`, img: prefix(this.push(new Map([[k, ONE]]), String(s.b1)), 0) })),
        ...this.atomsAt[X2].map(k => ({ key: `2|${k}`, img: prefix(scale(this.push(new Map([[k, ONE]]), String(s.b2)), MINUS_ONE), 0) })),
      ];
      const ker = this.kernel(dom, [T]);
      if (!ker.length) continue;
      const tb = this.space([X1, X2]);
      for (const a of this.atomsAt[P]) {
        const e = new Map([[a, ONE]]);
        const img = prefix(this.push(e, String(s.a1)), 0);
        for (const [kk, c] of prefix(this.push(e, String(s.a2)), 1)) img.set(kk, c);
        tb.insert(img, new Map());
      }
      for (const { lam, cert } of ker) {
        if (!room()) break;
        const u = new Map(), w = new Map(), pair = new Map();
        for (const [k, c] of lam) {
          if (k.startsWith('1|')) { u.set(k.slice(2), c); pair.set(`0|${k.slice(2)}`, c); }
          else { w.set(k.slice(2), c); pair.set(`1|${k.slice(2)}`, c); }
        }
        const r = tb.insert(pair, new Map());
        if (r.vec.size === 0) continue;
        const step = { kind: 'pbLift', hyp: h, u, w, cert: unprefix(cert) };
        this.steps.push(step);
        const x = this.newVar(P, null, this.steps.length - 1);
        step.newVar = x;
        step.fact1 = this.addFact(X1, axpy(this.push(this.varVec(x), String(s.a1)), MINUS_ONE, u), { how: 'pbLift', step: this.steps.length - 1 });
        step.fact2 = this.addFact(X2, axpy(this.push(this.varVec(x), String(s.a2)), MINUS_ONE, w), { how: 'pbLift', step: this.steps.length - 1 });
        added++;
      }
    }
    // pushouts
    for (const h of this.hyps.po) {
      const s = h.sq;
      const P = A[s.a1].src, X1 = A[s.a1].dst, X2 = A[s.a2].dst, T = A[s.b1].dst;
      // cover
      const tb = this.space([T]);
      for (const a of this.atomsAt[X1]) tb.insert(prefix(this.push(new Map([[a, ONE]]), String(s.b1)), 0), new Map());
      for (const a of this.atomsAt[X2]) tb.insert(prefix(this.push(new Map([[a, ONE]]), String(s.b2)), 0), new Map());
      for (const k of [...this.atomsAt[T]]) {
        if (!room()) break;
        const v = new Map([[k, ONE]]);
        const r = tb.insert(prefix(v, 0), new Map());
        if (r.vec.size === 0) continue;
        const step = { kind: 'poCover', hyp: h, v };
        this.steps.push(step);
        const b = this.newVar(X1, null, this.steps.length - 1);
        const c = this.newVar(X2, null, this.steps.length - 1);
        step.newVars = [b, c];
        const vec = axpy(axpy(this.push(this.varVec(b), String(s.b1)), ONE, this.push(this.varVec(c), String(s.b2))), MINUS_ONE, v);
        step.fact = this.addFact(T, vec, { how: 'poCover', step: this.steps.length - 1 });
        added++;
      }
      // relations: pairs (u, w) with b1 u + b2 w = 0
      const dom = [
        ...this.atomsAt[X1].map(k => ({ key: `1|${k}`, img: prefix(this.push(new Map([[k, ONE]]), String(s.b1)), 0) })),
        ...this.atomsAt[X2].map(k => ({ key: `2|${k}`, img: prefix(this.push(new Map([[k, ONE]]), String(s.b2)), 0) })),
      ];
      const ker = this.kernel(dom, [T]);
      if (!ker.length) continue;
      const tb2 = this.space([X1, X2]);
      for (const a of this.atomsAt[P]) {
        const e = new Map([[a, ONE]]);
        const img = prefix(this.push(e, String(s.a1)), 0);
        for (const [kk, c] of prefix(scale(this.push(e, String(s.a2)), MINUS_ONE), 1)) img.set(kk, c);
        tb2.insert(img, new Map());
      }
      for (const { lam, cert } of ker) {
        if (!room()) break;
        const u = new Map(), w = new Map(), pair = new Map();
        for (const [k, c] of lam) {
          if (k.startsWith('1|')) { u.set(k.slice(2), c); pair.set(`0|${k.slice(2)}`, c); }
          else { w.set(k.slice(2), c); pair.set(`1|${k.slice(2)}`, c); }
        }
        const r = tb2.insert(pair, new Map());
        if (r.vec.size === 0) continue;
        const step = { kind: 'poRel', hyp: h, u, w, cert: unprefix(cert) };
        this.steps.push(step);
        const x = this.newVar(P, null, this.steps.length - 1);
        step.newVar = x;
        step.fact1 = this.addFact(X1, axpy(this.push(this.varVec(x), String(s.a1)), MINUS_ONE, u), { how: 'poRel', step: this.steps.length - 1 });
        // a2 x = -w  -> a2 x + w = 0
        step.fact2 = this.addFact(X2, axpy(this.push(this.varVec(x), String(s.a2)), ONE, w), { how: 'poRel', step: this.steps.length - 1 });
        added++;
      }
    }
    // unfold zigzag-defined maps on every element of their source
    for (const z of this.hyps.zigzag || []) {
      for (const k of [...this.atomsAt[z.X]]) {
        const key = `${z.arrow}:${k}`;
        if (this.unfolded.has(key)) continue;
        if (!room()) break;
        this.unfolded.add(key);
        this.unfold(z, new Map([[k, ONE]]));
        added++;
      }
    }
    return added;
  }

  /** δ(v) = y_n where (v, y_1, ..., y_n) is a chosen solution of the zigzag */
  unfold(z, v) {
    const step = { kind: 'unfold', hyp: z, v, newVars: [], facts: [] };
    this.steps.push(step);
    const si = this.steps.length - 1;
    let prev = v;
    z.steps.forEach((st, j) => {
      const y = this.newVar(z.objs[j + 1], null, si);
      step.newVars.push(y);
      const yv = this.varVec(y);
      let f;
      if (st.dir === 'fwd') f = this.addFact(z.objs[j + 1], axpy(this.push(prev, String(st.arrow)), MINUS_ONE, yv), { how: 'unfold', step: si });
      else f = this.addFact(z.objs[j], axpy(this.push(yv, String(st.arrow)), MINUS_ONE, prev), { how: 'unfold', step: si });
      step.facts.push(f);
      prev = yv;
    });
    step.defFact = this.addFact(z.Y, axpy(this.push(v, String(z.arrow)), MINUS_ONE, prev), { how: 'unfold', step: si });
    return step;
  }

  // ------------------------------------------------------------ goals

  /** goal: {kind:'zero', obj, vec} or {kind:'image', obj, vec, src, path} */
  check(goal) {
    if (goal.kind === 'zero') {
      const cert = this.inK(goal.obj, goal.vec);
      return cert ? { ...goal, cert } : null;
    }
    const r = this.solveImage(goal.vec, goal.obj, goal.src, goal.path);
    return r ? { ...goal, t: r.t, cert: r.cert } : null;
  }

  run(goal) {
    for (let round = 0; ; round++) {
      this.saturate();
      const done = this.check(goal);
      if (done) return { status: 'proved', result: done, rounds: round };
      if (round >= this.opts.maxRounds || this.vars.length >= this.opts.maxVars) {
        return { status: 'unknown', reason: 'search budget exhausted' };
      }
      const n = this.existentialRound();
      if (n === 0 && this.truncated) return { status: 'unknown', reason: 'search budget exhausted' };
      if (n === 0) {
        this.saturate();
        const again = this.check(goal);
        if (again) return { status: 'proved', result: again, rounds: round };
        return { status: 'refuted', counterexample: this.counterexample(goal) };
      }
    }
  }

  // ------------------------------------------------------------ counterexample

  /** quotient spaces E_B/K_B with bases (non-pivot atoms) and matrices of the solid arrows */
  counterexample(goal) {
    const D = this.D;
    const bases = D.objs.map((o, i) => this.atomsAt[i].filter(k => !this.K[i].rows.has(k)));
    const dims = bases.map(b => b.length);
    const coord = (obj, vec) => {
      const r = this.K[obj].reduce(vec);
      return bases[obj].map(k => r.vec.get(k) || new Q(0));
    };
    const matrices = [];
    for (const i of this.phase.arrowSet) {
      const a = D.arrows[i];
      const cols = bases[a.src].map(k => coord(a.dst, this.push(new Map([[k, ONE]]), String(i))));
      // rows = dims[dst], cols = dims[src]
      const M = [];
      for (let r = 0; r < dims[a.dst]; r++) M.push(cols.map(c => c[r]));
      matrices.push({ arrow: i, rows: dims[a.dst], cols: dims[a.src], M });
    }
    let witness = null;
    if (goal) witness = { obj: goal.obj, coords: coord(goal.obj, goal.vec) };
    return { dims, bases, matrices, witness };
  }
}

// ------------------------------------------------------------ helpers

export function prefix(v, i) {
  const out = new Map();
  for (const [k, c] of v) out.set(`${i}|${k}`, c);
  return out;
}

/** strip the component prefix; if comp given, keep only that component */
export function unprefix(v, comp = null) {
  const out = new Map();
  for (const [k, c] of v) {
    const bar = k.indexOf('|');
    const i = Number(k.slice(0, bar));
    if (comp !== null && i !== comp) continue;
    addTo(out, k.slice(bar + 1), c);
  }
  return out;
}

export function certEntries(cert) {
  // key F<id>#<path>
  return [...cert].map(([k, c]) => {
    const m = /^F(\d+)#(.*)$/.exec(k);
    return { fact: Number(m[1]), path: m[2], coef: c };
  });
}

export function varsOfVec(chase, vec) {
  const s = new Set();
  for (const k of vec.keys()) s.add(chase.atoms.get(k).varId);
  return s;
}

export { parseKey };
