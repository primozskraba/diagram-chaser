// Orchestration: queries -> chases -> human proof + Lean 4 theorem & proof.
import { compile, Phase, baseZeroGens, baseGenerators, dashedConstraints, pathKey, parseKey, comparePaths } from './diagram.js';
import { Chase } from './engine.js';
import { ZERO, ONE, MINUS_ONE } from './rational.js';
import { axpy } from './linalg.js';
import * as L from './lean.js';

const { sub } = L;
const STD_SIMP = ['map_add', 'map_sub', 'map_neg', 'map_zero', 'map_zsmul', 'map_nsmul', 'LinearMap.comp_apply', 'LinearMap.zero_apply', 'LinearMap.id_apply'];

class Names {
  constructor(used) { this.used = new Set(used); }
  fresh(base) {
    if (!this.used.has(base)) { this.used.add(base); return base; }
    for (let n = 1; ; n++) {
      const c = `${base}${sub(n)}`;
      if (!this.used.has(c)) { this.used.add(c); return c; }
    }
  }
  numbered(base) {
    for (let n = 1; ; n++) {
      const c = `${base}${sub(n)}`;
      if (!this.used.has(c)) { this.used.add(c); return c; }
    }
  }
}

const safeSuffix = (s) => (/^[A-Za-z0-9_'α-ωΑ-Ω₀-₉]+$/.test(s) && !/[λΠΣ]/.test(s) ? s : null);

// ------------------------------------------------------------------ setup

function assignHyps(D, names) {
  const H = { arrow: new Map(), exact: [], pb: [], po: [], zigzag: new Map() };
  for (const a of D.arrows) {
    if (a.dashed) continue;
    const suf = safeSuffix(a.name.replace(/[«»]/g, '')) || `map${a.i}`;
    if (a.equal) {
      // an identity: the source and target are the same Lean type
      const n = names.fresh(`h${suf}`);
      H.arrow.set(a.i, { name: n, stmt: `${a.lean} = LinearMap.id`, mono: `(DC.injective_of_eq_id ${n})`, epi: `(DC.surjective_of_eq_id ${n})`, equal: true });
    } else if (a.mono && a.epi) {
      const n = names.fresh(`h${suf}`);
      H.arrow.set(a.i, { name: n, stmt: `Function.Bijective ${a.lean}`, mono: `${n}.1`, epi: `${n}.2` });
    } else if (a.mono) {
      const n = names.fresh(`h${suf}`);
      H.arrow.set(a.i, { name: n, stmt: `Function.Injective ${a.lean}`, mono: n });
    } else if (a.epi) {
      const n = names.fresh(`h${suf}`);
      H.arrow.set(a.i, { name: n, stmt: `Function.Surjective ${a.lean}`, epi: n });
    }
    if (a.zero) {
      const n = names.fresh(`h${suf}0`);
      H.arrow.set(a.i, { ...(H.arrow.get(a.i) || {}), zeroName: n, zeroStmt: `${a.lean} = 0` });
    }
  }
  D.exact.forEach((e) => H.exact.push({ ...e, ref: names.numbered('hex') }));
  D.squares.forEach((s) => {
    if (s.type === 'pullback') H.pb.push({ sq: s, ref: names.numbered('hpb') });
    else H.po.push({ sq: s, ref: names.numbered('hpo') });
  });
  return H;
}

function engineHyps(D, H, arrowSet) {
  const mono = [], epi = [];
  for (const [i, h] of H.arrow) {
    if (!arrowSet.has(i)) continue;
    if (h.mono) mono.push({ arrow: i, ref: h.mono });
    if (h.epi) epi.push({ arrow: i, ref: h.epi });
  }
  return {
    mono, epi,
    exact: H.exact.filter(e => arrowSet.has(e.first) && arrowSet.has(e.second)),
    pb: H.pb, po: H.po,
    zigzag: [...H.zigzag.values()].filter(z => arrowSet.has(z.arrow)),
  };
}

// ------------------------------------------------------------------ proof context

class Ctx {
  constructor(D, names, opts) {
    this.D = D;
    this.names = names;
    this.opts = opts;
    this.binder = names.fresh('x');
    this.binder2 = names.fresh('y');
    this.ePrefix = ['e', 'eq', 'hh', 'ee'].find(p => ![1, 2, 3, 4, 5, 6, 7, 8, 9].some(n => names.used.has(`${p}${sub(n)}`)));
    this.ruleNames = new Map(); // ruleKey -> lean name
    this.lean = []; // lines of the proof body (indent 2 base)
    this.human = []; // [{title, lines}]
    this.factNo = 0;
  }

  simpFor(phase) {
    const names = phase.rules().map(r => this.ruleNames.get(ruleKey(r)) || r.proof.zgen).filter(Boolean);
    return STD_SIMP.concat([...new Set(names)]).join(', ');
  }

  /** emit `have` lines for the rewrite rules of a phase that were not emitted before */
  emitRules(phase, indent = 2) {
    const D = this.D, x = this.binder;
    const out = [];
    for (const r of phase.rules()) {
      const key = ruleKey(r);
      if (this.ruleNames.has(key)) continue;
      if (r.proof.kind === 'zgen') { this.ruleNames.set(key, r.proof.zgen); continue; }
      const st = r.proof.steps;
      if (r.proof.kind === 'eq' && st.length === 1 && st[0].dir === 'fwd' && pathKey(st[0].from) === pathKey(r.lhs) && pathKey(st[0].to) === pathKey(r.rhs)) {
        this.ruleNames.set(key, st[0].name); continue;
      }
      const name = this.names.numbered('r');
      this.ruleNames.set(key, name);
      const lhs = L.applyLean(D, r.lhs, x);
      const rhs = r.rhs === null ? '0' : L.applyLean(D, r.rhs, x);
      const rw = r.proof.steps.map(s => (s.dir === 'fwd' ? s.name : `← ${s.name}`)).join(', ');
      if (r.proof.kind === 'eq') {
        out.push(`have ${name} : ∀ ${x}, ${lhs} = ${rhs} := fun ${x} => by conv_lhs => rw [${rw}]`);
      } else {
        out.push(`have ${name} : ∀ ${x}, ${lhs} = 0 := fun ${x} => by`);
        out.push(`  conv_lhs => rw [${rw}]`);
        out.push(`  simp only [${r.proof.zgen}, map_zero]`);
      }
    }
    return L.indentLines(out, indent);
  }
}

const ruleKey = (r) => `${pathKey(r.lhs)}=>${r.rhs === null ? '0' : pathKey(r.rhs)}`;

// ------------------------------------------------------------------ chase emission

/**
 * Run a chase. setup(chase) creates intro variables/facts and returns
 * {goal, factRefs: Map(factId -> Lean ref), humanIntro: [..]}.
 */
function runChase(ctx, phase, H, setup) {
  const D = ctx.D;
  const chase = new Chase(D, phase, engineHyps(D, H, phase.arrowSet), {
    fresh: (b) => ctx.names.fresh(b), maxRounds: ctx.opts.maxRounds, maxVars: ctx.opts.maxVars,
  });
  const s = setup(chase);
  const res = chase.run(s.goal);
  return { chase, phase, ...s, res };
}

/**
 * Lean + human lines for the pruned steps of a successful chase, followed
 * by the finishing tactic. Returns {lean: [...], human: [...]}.
 * finish: 'zero' (goal is `... = 0` already), 'exists' (goal ∃ t, φ t = y / y ∈ range),
 *         'memRange' (goal y ∈ LinearMap.range φ)
 */
function emitChase(ctx, run, finish, opts = {}) {
  const { chase } = run;
  const D = ctx.D;
  const result = run.res.result;
  const simp = ctx.simpFor(run.phase);
  const refs = new Map(run.factRefs);
  const factNo = new Map();
  const lean = [], human = [];
  for (const [fid] of run.introHuman || []) {
    if (fid >= 0) factNo.set(fid, ++ctx.factNo);
  }
  const dctx = { chase, simp, ePrefix: ctx.ePrefix, factRef: (fid) => refs.get(fid) };
  const V = (v) => L.vecLean(chase, v);
  const Hm = (v) => L.vecHuman(chase, v);
  const cite = (cert) => {
    const es = [...cert.keys()].map(k => /^F(\d+)#(.*)$/.exec(k));
    const nums = [...new Set(es.map(m => factNo.get(Number(m[1]))).filter(Boolean))].sort((a, b) => a - b);
    const comm = es.some(m => m[2] !== '');
    const parts = nums.map(n => `(${n})`);
    if (comm) parts.push('commutativity');
    return parts.length ? ` [by ${parts.join(', ')}]` : '';
  };
  const name = (f) => { const n = ++ctx.factNo; factNo.set(f.id, n); return n; };
  const hname = () => ctx.names.fresh('h');
  const arrowName = (i) => D.arrows[i].name;
  const objName = (i) => (D.objs[i].kind === 'zero' ? '0' : D.objs[i].name);

  for (const line of run.introHuman || []) human.push(line[1].replace('{n}', `(${factNo.get(line[0])})`));

  const needed = L.neededSteps(chase, opts.certs || [result.cert], opts.vecs || [result.vec, result.t].filter(Boolean));
  for (const idx of needed) {
    const s = chase.steps[idx];
    switch (s.kind) {
      case 'inj': {
        const a = D.arrows[s.arrow];
        const h = hname();
        const goalLine = L.byTerm(L.deriveTactic(dctx, s.cert), 4);
        lean.push(`have ${h} : ${V(s.v)} = 0 := DC.inj0 ${s.hyp.ref} ${goalLine}`);
        refs.set(s.fact.id, h);
        const n = name(s.fact);
        human.push(`${a.name}(${Hm(s.v)}) = 0${cite(s.cert)}; since ${a.name} is ${a.equal ? 'the identity' : 'injective'}, ${Hm(s.v)} = 0.   (${n})`);
        break;
      }
      case 'zeroObj': {
        const h = hname();
        lean.push(`have ${h} : ${V(s.v)} = 0 := Subsingleton.elim _ _`);
        refs.set(s.fact.id, h);
        human.push(`${Hm(s.v)} = 0 since it lies in the zero module.   (${name(s.fact)})`);
        break;
      }
      case 'pbSep': {
        const h = hname();
        const sq = s.hyp.sq;
        lean.push(`have ${h} : ${V(s.v)} = 0 := ${s.hyp.ref}.sep _ ${L.byTerm(L.deriveTactic(dctx, s.cert1), 4)} ${L.byTerm(L.deriveTactic(dctx, s.cert2), 4)}`);
        refs.set(s.fact.id, h);
        human.push(`${arrowName(sq.a1)}(${Hm(s.v)}) = 0${cite(s.cert1)} and ${arrowName(sq.a2)}(${Hm(s.v)}) = 0${cite(s.cert2)}; by the pullback property ${Hm(s.v)} = 0.   (${name(s.fact)})`);
        break;
      }
      case 'exactLift': {
        const h = hname();
        const psi = D.arrows[s.hyp.first], phi = D.arrows[s.hyp.second];
        lean.push(`obtain ⟨${s.newVar.name}, ${h}⟩ := (${s.hyp.ref} (${V(s.v)})).mp ${L.byTerm(L.deriveTactic(dctx, s.cert), 4)}`);
        refs.set(s.fact.id, `(sub_eq_zero.mpr ${h})`);
        const n = name(s.fact);
        human.push(`${phi.name}(${Hm(s.v)}) = 0${cite(s.cert)}; by exactness at ${objName(psi.dst)} there is ${s.newVar.name} ∈ ${objName(psi.src)} with ${psi.name}(${s.newVar.name}) = ${Hm(s.v)}.   (${n})`);
        break;
      }
      case 'epiLift': {
        const h = hname();
        const phi = D.arrows[s.hyp.arrow];
        lean.push(`obtain ⟨${s.newVar.name}, ${h}⟩ := ${s.hyp.ref} (${V(s.v)})`);
        refs.set(s.fact.id, `(sub_eq_zero.mpr ${h})`);
        if (phi.equal) human.push(`${phi.name} is the identity: take ${s.newVar.name} = ${Hm(s.v)} ∈ ${objName(phi.src)}, so ${phi.name}(${s.newVar.name}) = ${Hm(s.v)}.   (${name(s.fact)})`);
        else human.push(`Since ${phi.name} is surjective, choose ${s.newVar.name} ∈ ${objName(phi.src)} with ${phi.name}(${s.newVar.name}) = ${Hm(s.v)}.   (${name(s.fact)})`);
        break;
      }
      case 'pbLift': {
        const h1 = hname(), h2 = hname();
        const sq = s.hyp.sq;
        lean.push(`obtain ⟨${s.newVar.name}, ${h1}, ${h2}⟩ := ${s.hyp.ref}.lift (${V(s.u)}) (${V(s.w)}) ${L.byTerm(L.deriveTactic(dctx, s.cert), 4)}`);
        refs.set(s.fact1.id, `(sub_eq_zero.mpr ${h1})`);
        refs.set(s.fact2.id, `(sub_eq_zero.mpr ${h2})`);
        const n1 = name(s.fact1), n2 = name(s.fact2);
        human.push(`${arrowName(sq.b1)}(${Hm(s.u)}) = ${arrowName(sq.b2)}(${Hm(s.w)})${cite(s.cert)}; by the pullback property there is ${s.newVar.name} ∈ ${objName(D.arrows[sq.a1].src)} with ${arrowName(sq.a1)}(${s.newVar.name}) = ${Hm(s.u)} and ${arrowName(sq.a2)}(${s.newVar.name}) = ${Hm(s.w)}.   (${n1}), (${n2})`);
        break;
      }
      case 'poCover': {
        const h = hname();
        const sq = s.hyp.sq;
        const [b, c] = s.newVars;
        lean.push(`obtain ⟨${b.name}, ${c.name}, ${h}⟩ := ${s.hyp.ref}.cover (${V(s.v)})`);
        refs.set(s.fact.id, `(sub_eq_zero.mpr ${h})`);
        human.push(`By the pushout property write ${Hm(s.v)} = ${arrowName(sq.b1)}(${b.name}) + ${arrowName(sq.b2)}(${c.name}).   (${name(s.fact)})`);
        break;
      }
      case 'poRel': {
        const h1 = hname(), h2 = hname();
        const sq = s.hyp.sq;
        lean.push(`obtain ⟨${s.newVar.name}, ${h1}, ${h2}⟩ := ${s.hyp.ref}.rel (${V(s.u)}) (${V(s.w)}) ${L.byTerm(L.deriveTactic(dctx, s.cert), 4)}`);
        refs.set(s.fact1.id, `(sub_eq_zero.mpr ${h1})`);
        refs.set(s.fact2.id, `(sub_eq_zero.mpr ${h2})`);
        const n1 = name(s.fact1), n2 = name(s.fact2);
        human.push(`${arrowName(sq.b1)}(${Hm(s.u)}) + ${arrowName(sq.b2)}(${Hm(s.w)}) = 0${cite(s.cert)}; by the pushout property there is ${s.newVar.name} with ${arrowName(sq.a1)}(${s.newVar.name}) = ${Hm(s.u)} and ${arrowName(sq.a2)}(${s.newVar.name}) = −(${Hm(s.w)}).   (${n1}), (${n2})`);
        break;
      }
      case 'unfold': {
        const z = s.hyp, n = z.steps.length, ys = s.newVars;
        const g = [], Hm1 = [];
        g[n] = hname();
        lean.push(`obtain ⟨${ys[n - 1].name}, ${g[n]}⟩ := ${z.tot} (${V(s.v)})`);
        for (let j = n; j >= 2; j--) {
          g[j - 1] = hname(); Hm1[j] = hname();
          lean.push(`obtain ⟨${ys[j - 2].name}, ${g[j - 1]}, ${Hm1[j]}⟩ := DC.mem_relComp.mp ${g[j]}`);
        }
        Hm1[1] = g[1];
        const parts = [];
        z.steps.forEach((st, j) => {
          const lem = st.dir === 'fwd' ? 'DC.mem_rel' : 'DC.mem_relInv';
          refs.set(s.facts[j].id, `(sub_eq_zero.mpr (${lem}.mp ${Hm1[j + 1]}))`);
          const prev = j === 0 ? Hm(s.v) : ys[j - 1].name;
          parts.push(st.dir === 'fwd' ? `${ys[j].name} = ${arrowName(st.arrow)}(${prev})` : `${arrowName(st.arrow)}(${ys[j].name}) = ${prev}`);
        });
        refs.set(s.defFact.id, `(sub_eq_zero.mpr (${z.def} _ _ ${g[n]}))`);
        const nums = [...s.facts, s.defFact].map(f => name(f));
        human.push(`Unfold ${arrowName(z.arrow)} at ${Hm(s.v)}: choose ${parts.join(', ')}; then ${arrowName(z.arrow)}(${Hm(s.v)}) = ${ys[n - 1].name}.   ${nums.map(k => `(${k})`).join(', ')}`);
        break;
      }
      default: throw new Error(`unknown step ${s.kind}`);
    }
  }
  if (finish === 'none') return { lean, human, dctx, V, Hm, cite };
  // finishing
  if (finish === 'zero') {
    lean.push(...L.deriveTactic(dctx, result.cert));
    if (result.vec.size === 0) human.push('This holds by commutativity of the diagram.');
    else human.push(`Hence ${Hm(result.vec)} = 0${cite(result.cert)}.`);
  } else {
    const t = V(result.t);
    const inner = L.byTerm(L.deriveTactic(dctx, result.cert), 4);
    const pathH = run.pathHuman;
    if (finish === 'exists') lean.push(`exact ⟨${t}, sub_eq_zero.mp ${inner}⟩`);
    else lean.push(`exact LinearMap.mem_range.mpr ⟨${t}, sub_eq_zero.mp ${inner}⟩`);
    human.push(`Hence ${Hm(result.vec)} = ${pathH}(${Hm(result.t)})${cite(result.cert)}.`);
  }
  return { lean, human };
}

// ------------------------------------------------------------------ goals (element setups)

/** intro a variable with no facts */
function introVar(chase, obj, name) {
  const v = chase.newVar(obj, null, -1);
  return v;
}

// ------------------------------------------------------------------ counterexample rendering

function renderCounterexample(ctx, run) {
  const D = ctx.D;
  const cx = identityBases(D, run.res.counterexample);
  const dims = D.objs.map((o, i) => ({ name: o.kind === 'zero' ? '0' : o.name, dim: cx.dims[i] }));
  const mats = cx.matrices.map(m => ({
    name: D.arrows[m.arrow].name,
    src: D.objs[D.arrows[m.arrow].src].name, dst: D.objs[D.arrows[m.arrow].dst].name,
    rows: m.rows, cols: m.cols, M: m.M.map(r => r.map(q => q.toString())),
  }));
  const witness = cx.witness ? { module: D.objs[cx.witness.obj].name, coords: cx.witness.coords.map(q => q.toString()) } : null;
  return { dims, matrices: mats, witness };
}

// small dense matrices over Q (arrays of rows)
const matMul = (A, B, n) => A.map(row => Array.from({ length: n }, (_, j) => row.reduce((acc, a, k) => acc.add(a.mul(B[k][j])), ZERO)));
const matId = (n) => Array.from({ length: n }, (_, i) => Array.from({ length: n }, (_, j) => (i === j ? ONE : ZERO)));
function matInv(A) {
  const n = A.length;
  const M = A.map((row, i) => [...row, ...matId(n)[i]]);
  for (let c = 0; c < n; c++) {
    const p = M.findIndex((row, r) => r >= c && !row[c].isZero());
    if (p < 0) return null;
    [M[c], M[p]] = [M[p], M[c]];
    const piv = M[c][c];
    M[c] = M[c].map(x => x.div(piv));
    for (let r = 0; r < n; r++) {
      if (r === c || M[r][c].isZero()) continue;
      const f = M[r][c];
      M[r] = M[r].map((x, j) => x.sub(f.mul(M[c][j])));
    }
  }
  return M.map(row => row.slice(n));
}

/**
 * Change bases in a counterexample so that every "=" map is an identity
 * matrix: modules identified by "=" get the basis transported from the first
 * module of their class. (The chase treats "=" as a bijection; this makes the
 * model literally satisfy the identifications.)
 */
function identityBases(D, cx) {
  const eqs = cx.matrices.filter(m => D.arrows[m.arrow].equal);
  if (!eqs.length) return cx;
  const T = D.objs.map(() => null); // columns: new basis in old coordinates
  for (let o = 0; o < D.objs.length; o++) {
    if (T[o]) continue;
    T[o] = matId(cx.dims[o]);
    const queue = [o];
    while (queue.length) {
      const u = queue.pop();
      for (const m of eqs) {
        const a = D.arrows[m.arrow];
        if (a.src === u && !T[a.dst]) { T[a.dst] = matMul(m.M, T[u], cx.dims[u]); queue.push(a.dst); }
        else if (a.dst === u && !T[a.src]) {
          const inv = matInv(m.M);
          if (!inv) return cx; // not bijective: leave the model as it is
          T[a.src] = matMul(inv, T[u], cx.dims[u]); queue.push(a.src);
        }
      }
    }
  }
  const Tinv = T.map(t => matInv(t));
  if (Tinv.some(t => !t)) return cx;
  const matrices = cx.matrices.map(m => {
    const a = D.arrows[m.arrow];
    if (!m.rows || !m.cols) return m;
    return { ...m, M: matMul(matMul(Tinv[a.dst], m.M, m.cols), T[a.src], m.cols) };
  });
  let witness = cx.witness;
  if (witness && witness.coords.length) {
    witness = { ...witness, coords: matMul(Tinv[witness.obj], witness.coords.map(c => [c]), 1).map(r => r[0]) };
  }
  return { ...cx, matrices, witness };
}

// ------------------------------------------------------------------ dashed (induced) arrows

function minPath(D, phase, u, v) {
  const list = phase.from[u].filter(r => r.dst === v).map(r => r.arr).sort((a, b) => comparePaths(D, a, b));
  return list[0] || null;
}

function arrowsInPaths(paths) { const s = new Set(); for (const p of paths) for (const i of p) s.add(i); return s; }

/**
 * Try to construct dashed arrow d on top of available arrow set S with generators G.
 * Returns a record or {ok:false,...}.
 */
function tryConstruct(ctx, H, d, S, G, zgens) {
  const D = ctx.D;
  const a = D.arrows[d];
  const X = a.src, Y = a.dst;
  const phase = new Phase(D, S, G, zgens);
  const cands = [];
  const direct = minPath(D, phase, X, Y);
  if (direct) cands.push({ how: 'direct', lhs: [d], rhs: direct });
  for (const i of S) {
    const b = D.arrows[i];
    const h = H.arrow.get(i);
    if (b.src === Y && h && h.mono) {
      const Phi = minPath(D, phase, X, b.dst);
      if (Phi) cands.push({ how: 'mono', via: i, ref: h.mono, lhs: [d, i], rhs: Phi });
    }
  }
  for (const i of S) {
    const b = D.arrows[i];
    const h = H.arrow.get(i);
    if (b.dst === X && h && h.epi) {
      const Psi = minPath(D, phase, b.src, Y);
      if (Psi) cands.push({ how: 'epi', via: i, ref: h.epi, lhs: [i, d], rhs: Psi });
    }
  }
  let refuted = null, lastUnknown = null;
  for (const c of cands) {
    let run = null;
    if (c.how === 'mono') {
      run = runChase(ctx, phase, H, (chase) => {
        const x = introVar(chase, X);
        const vec = chase.push(chase.varVec(x), pathKey(c.rhs));
        return {
          goal: { kind: 'image', obj: D.arrows[c.via].dst, vec, src: Y, path: String(c.via) },
          factRefs: new Map(), x, pathHuman: D.arrows[c.via].name,
          introHuman: [[-1, `Let ${x.name} ∈ ${D.objs[X].name}; we show ${L.applyHuman(D, c.rhs, x.name)} lies in the image of ${D.arrows[c.via].name}.`]],
        };
      });
    } else if (c.how === 'epi') {
      run = runChase(ctx, phase, H, (chase) => {
        const w = introVar(chase, D.arrows[c.via].src);
        const hw = ctx.names.fresh('hw');
        const f = chase.addFact(X, chase.push(chase.varVec(w), String(c.via)), { how: 'intro', step: -1 });
        return {
          goal: { kind: 'zero', obj: Y, vec: chase.push(chase.varVec(w), pathKey(c.rhs)) },
          factRefs: new Map([[f.id, hw]]), w, hw,
          introHuman: [[f.id, `Let ${w.name} ∈ ${D.objs[w.obj].name} with ${D.arrows[c.via].name}(${w.name}) = 0 {n}; we show ${L.applyHuman(D, c.rhs, w.name)} = 0.`]],
        };
      });
    }
    if (run && run.res.status !== 'proved') {
      if (run.res.status === 'refuted') refuted = { cand: c, run };
      else lastUnknown = { cand: c, run };
      if (refuted) break;
      continue;
    }
    return { ok: true, cand: c, run, phase };
  }
  if (!refuted) {
    const zz = tryZigzags(ctx, H, d, phase);
    if (zz) return zz;
  }
  if (!cands.length) {
    return { ok: false, status: 'unknown', reason: `No way to construct ${a.name}: there is no injective map out of ${D.objs[Y].name}, no surjective map into ${D.objs[X].name}, no path ${D.objs[X].name} → ${D.objs[Y].name}, and no zigzag through the diagram (up to ${ZIGZAG_MAX} steps) that defines it.` };
  }
  if (refuted) return { ok: false, status: 'refuted', reason: `${a.name} cannot exist in general: ${refuted.cand.how === 'mono' ? `${L.applyHuman(D, refuted.cand.rhs, '–')} does not land in the image of ${D.arrows[refuted.cand.via].name}` : `${L.applyHuman(D, refuted.cand.rhs, '–')} does not vanish on the kernel of ${D.arrows[refuted.cand.via].name}`}.`, run: refuted.run };
  return { ok: false, status: 'unknown', reason: `Could not construct ${a.name} within the search budget.`, run: lastUnknown && lastUnknown.run };
}

// ------------------------------------------------------------------ zigzag-defined maps

const ZIGZAG_MAX = 6;

/** zigzags X — … — Y in the arrow set: steps forward along a map or backward against it */
function findZigzags(D, S, X, Y, maxLen = ZIGZAG_MAX, limit = 40) {
  const adj = D.objs.map(() => []);
  for (const i of S) {
    const a = D.arrows[i];
    adj[a.src].push({ arrow: i, dir: 'fwd', to: a.dst });
    adj[a.dst].push({ arrow: i, dir: 'bwd', to: a.src });
  }
  const res = [];
  let budget = 20000;
  const walk = (v, steps, seen) => {
    if (--budget < 0) return;
    if (v === Y) { if (steps.some(st => st.dir === 'bwd')) res.push(steps.slice()); return; }
    if (steps.length >= maxLen) return;
    for (const e of adj[v]) {
      if (seen.has(e.to) || (D.objs[e.to].kind === 'zero' && e.to !== Y)) continue;
      seen.add(e.to); steps.push(e);
      walk(e.to, steps, seen);
      steps.pop(); seen.delete(e.to);
    }
  };
  walk(X, [], new Set([X]));
  const nb = (z) => z.filter(st => st.dir === 'bwd').length;
  res.sort((p, q) => p.length - q.length || nb(p) - nb(q));
  return res.slice(0, limit);
}

function zigzagObjs(D, X, steps) {
  const objs = [X];
  for (const st of steps) objs.push(st.dir === 'fwd' ? D.arrows[st.arrow].dst : D.arrows[st.arrow].src);
  return objs;
}

function zigzagLean(D, steps) {
  let g = null;
  for (const st of steps) {
    const r = `DC.${st.dir === 'fwd' ? 'rel' : 'relInv'} ${D.arrows[st.arrow].lean}`;
    g = g === null ? r : `DC.relComp (${g}) (${r})`;
  }
  return g;
}

function zigzagHuman(D, X, steps) {
  const nm = (o) => (D.objs[o].kind === 'zero' ? '0' : D.objs[o].name);
  let out = nm(X);
  for (const st of steps) {
    const a = D.arrows[st.arrow];
    out += st.dir === 'fwd' ? ` —${a.name}→ ${nm(a.dst)}` : ` ←${a.name}— ${nm(a.src)}`;
  }
  return out;
}

/**
 * Try the zigzags from X to Y: totality (every element has an image, choosing
 * lifts at the backward steps) and single-valuedness (0 relates only to 0).
 */
function tryZigzags(ctx, H, d, phase) {
  const D = ctx.D;
  const a = D.arrows[d];
  const X = a.src, Y = a.dst;
  for (const steps of findZigzags(D, phase.arrowSet, X, Y)) {
    const saved = new Set(ctx.names.used);
    const objs = zigzagObjs(D, X, steps);
    // totality
    const chase = new Chase(D, phase, engineHyps(D, H, phase.arrowSet), {
      fresh: (b) => ctx.names.fresh(b), maxRounds: ctx.opts.maxRounds, maxVars: ctx.opts.maxVars,
    });
    const x = chase.newVar(X, null, -1);
    const W = [chase.varVec(x)];
    const stages = [];
    let ok = true;
    steps.forEach((st, j) => {
      if (!ok) return;
      if (st.dir === 'fwd') { W.push(chase.push(W[j], String(st.arrow))); stages.push({ dir: 'fwd', cert: new Map() }); return; }
      const r = chase.run({ kind: 'image', obj: objs[j], vec: W[j], src: objs[j + 1], path: String(st.arrow) });
      if (r.status !== 'proved') { ok = false; return; }
      W.push(r.result.t);
      stages.push({ dir: 'bwd', cert: r.result.cert });
    });
    if (!ok) { ctx.names.used = saved; continue; }
    const tot = { chase, phase, factRefs: new Map(), res: { status: 'proved' }, x, W, stages, introHuman: [[-1, `Let ${x.name} ∈ ${D.objs[X].name}.`]] };
    // single-valuedness
    const sv = runChase(ctx, phase, H, (ch) => {
      const n = steps.length;
      const ys = objs.slice(1).map(o => ch.newVar(o, null, -1));
      const hy = ctx.names.fresh('hy');
      const g = [], Hs = [], introLean = [];
      g[n] = hy;
      for (let j = n; j >= 2; j--) {
        g[j - 1] = ctx.names.fresh('hg'); Hs[j] = ctx.names.fresh('hs');
        introLean.push(`obtain ⟨${ys[j - 2].name}, ${g[j - 1]}, ${Hs[j]}⟩ := DC.mem_relComp.mp ${g[j]}`);
      }
      Hs[1] = g[1];
      const factRefs = new Map(), introHuman = [[-1, `Suppose 0 ∈ ${D.objs[X].kind === 'zero' ? '0' : D.objs[X].name} is related to ${ys[n - 1].name}:`]];
      let prev = new Map();
      steps.forEach((st, j) => {
        const yv = ch.varVec(ys[j]);
        const an = D.arrows[st.arrow].name;
        const prevH = j === 0 ? '0' : ys[j - 1].name;
        let f;
        if (st.dir === 'fwd') {
          f = ch.addFact(objs[j + 1], axpy(ch.push(prev, String(st.arrow)), MINUS_ONE, yv), { how: 'intro', step: -1 });
          factRefs.set(f.id, `(sub_eq_zero.mpr (DC.mem_rel.mp ${Hs[j + 1]}))`);
          introHuman.push([f.id, `${ys[j].name} = ${an}(${prevH}) {n}`]);
        } else {
          f = ch.addFact(objs[j], axpy(ch.push(yv, String(st.arrow)), MINUS_ONE, prev), { how: 'intro', step: -1 });
          factRefs.set(f.id, `(sub_eq_zero.mpr (DC.mem_relInv.mp ${Hs[j + 1]}))`);
          introHuman.push([f.id, `${an}(${ys[j].name}) = ${prevH} {n}`]);
        }
        prev = yv;
      });
      const yn = ys[n - 1];
      return { goal: { kind: 'zero', obj: Y, vec: ch.varVec(yn) }, factRefs, introHuman, introLean, yn, hy };
    });
    if (sv.res.status !== 'proved') { ctx.names.used = saved; continue; }
    const cand = { how: 'zigzag', steps, objs, deps: steps.map(st => st.arrow), rhs: [] };
    return { ok: true, cand, tot, sv, phase };
  }
  return null;
}

/**
 * Construct the needed dashed arrows, emitting Lean + human text.
 * Returns {ok, phase, S, G, records:[...]} or failure.
 */
function constructDashed(ctx, H, base, neededInit) {
  const D = ctx.D;
  const dashed = D.arrows.filter(a => a.dashed).map(a => a.i);
  if (!neededInit.size) return { ok: true, S: base.solid, G: base.gens, records: [] };
  // pass 1: construct everything possible to find dependencies (names used here are discarded)
  const savedNames = new Set(ctx.names.used);
  let S = new Set(base.solid), G = base.gens.slice();
  const order = [], info = new Map();
  let progress = true;
  const pending = new Set(dashed);
  while (progress) {
    progress = false;
    for (const d of [...pending]) {
      const r = tryConstruct(ctx, H, d, S, G, base.zgens);
      if (!r.ok) { info.set(d, r); continue; }
      const cons = dashedConstraints(D, new Set([...S, d]), d);
      order.push(d); pending.delete(d); progress = true;
      info.set(d, { ok: true, deps: arrowsInPaths([r.cand.rhs, r.cand.deps || [], ...cons.map(c => c.lhs), ...cons.map(c => c.rhs)]) });
      if (r.cand.how === 'zigzag') {
        H.zigzag.set(d, { arrow: d, X: D.arrows[d].src, Y: D.arrows[d].dst, steps: r.cand.steps, objs: r.cand.objs, tot: '_', def: '_' });
      }
      S = new Set([...S, d]);
      G = G.concat(cons.map(c => ({ p: c.lhs, q: c.rhs, name: null })));
    }
  }
  ctx.names.used = savedNames;
  // closure of needed
  const needed = new Set(neededInit);
  let grew = true;
  while (grew) {
    grew = false;
    for (const d of [...needed]) {
      const r = info.get(d);
      if (!r || !r.ok) continue;
      for (const i of r.deps) if (D.arrows[i].dashed && !needed.has(i)) { needed.add(i); grew = true; }
    }
  }
  for (const d of needed) {
    if (!order.includes(d)) {
      const r = info.get(d) || { reason: 'could not be constructed' };
      return { ok: false, arrow: d, ...r };
    }
  }
  // pass 2: construct needed arrows in order, emitting proofs
  S = new Set(base.solid); G = base.gens.slice();
  const records = [];
  for (const d of order.filter(i => needed.has(i))) {
    const a = D.arrows[d];
    const r = tryConstruct(ctx, H, d, S, G, base.zgens);
    if (!r.ok) return { ok: false, arrow: d, ...r };
    const rec = { arrow: d, cand: r.cand, lean: [], human: [] };
    const X = D.objs[a.src], Y = D.objs[a.dst];
    const T = `${X.lean} →ₗ[${L.RING}] ${Y.lean}`;
    const hdef = ctx.names.fresh(`h${safeSuffix(a.name) || 'd'}₀`);
    const c = r.cand;
    const title = `Construction of ${a.name} : ${X.name} → ${Y.name}`;
    const hum = [];
    const x = ctx.binder, yb = ctx.binder2;
    const Sd = new Set([...S, d]);
    rec.hdef = hdef;
    rec.conj = []; // [{stmt(nm), hname}] — first one characterises the map
    rec.pathCons = []; // path equalities through d, as generators
    let defGens = [];
    if (c.how === 'zigzag') {
      const Gx = zigzagLean(D, c.steps);
      const tot = ctx.names.fresh(`h${safeSuffix(a.name) || 'd'}_tot`);
      const T0 = r.tot;
      const V = (v) => L.vecLean(T0.chase, v);
      const Hv = (v) => L.vecHuman(T0.chase, v);
      const bwdCerts = T0.stages.map(st => st.cert);
      const em = emitChase(ctx, T0, 'none', { certs: bwdCerts, vecs: T0.W });
      const body = [...em.lean];
      const sn = [];
      const humStages = [];
      c.steps.forEach((st, j) => {
        const nm = ctx.names.fresh('s');
        sn.push(nm);
        const arr = [st.arrow];
        const stmt = st.dir === 'fwd' ? `${L.applyLean(D, arr, V(T0.W[j]))} = ${V(T0.W[j + 1])}` : `${L.applyLean(D, arr, V(T0.W[j + 1]))} = ${V(T0.W[j])}`;
        body.push(`have ${nm} : ${stmt} := sub_eq_zero.mp ${L.byTerm(L.deriveTactic(em.dctx, T0.stages[j].cert), 4)}`);
        const an = D.arrows[st.arrow].name;
        if (st.dir === 'bwd') humStages.push(`${an}(${Hv(T0.W[j + 1])}) = ${Hv(T0.W[j])}${em.cite(T0.stages[j].cert)}.`);
      });
      let mem = null;
      c.steps.forEach((st, j) => {
        const stepPf = `DC.${st.dir === 'fwd' ? 'mem_rel' : 'mem_relInv'}.mpr ${sn[j]}`;
        mem = j === 0 ? stepPf : `DC.mem_relComp.mpr ⟨${L.paren(V(T0.W[j]))}, ${mem}, ${stepPf}⟩`;
      });
      body.push(`exact ⟨${L.paren(V(T0.W[c.steps.length]))}, ${mem}⟩`);
      rec.lean.push(`have ${tot} : ∀ ${x}, ∃ ${yb}, (${x}, ${yb}) ∈ ${Gx} := fun ${T0.x.name} => by`);
      rec.lean.push(...L.indentLines(body, 2));
      const emS = emitChase(ctx, r.sv, 'zero');
      rec.lean.push(`obtain ⟨${a.lean}, ${hdef}⟩ : ∃ ${a.lean} : ${T}, ∀ ${x} ${yb}, (${x}, ${yb}) ∈ ${Gx} → ${a.lean} ${x} = ${yb} := DC.factor_rel _ ${tot} (fun ${r.sv.yn.name} ${r.sv.hy} => by`);
      rec.lean.push(...L.indentLines([...r.sv.introLean, ...emS.lean], 2).map((l, n, arr2) => (n === arr2.length - 1 ? l + ')' : l)));
      H.zigzag.set(d, { arrow: d, X: a.src, Y: a.dst, steps: c.steps, objs: c.objs, tot, def: hdef });
      rec.conj.push({ stmt: (nm) => `(∀ ${x} ${yb}, (${x}, ${yb}) ∈ ${Gx} → ${nm} ${x} = ${yb})`, hname: hdef });
      rec.uniq = (hd) => `DC.rel_unique ${tot} ${hdef} ${hd}`;
      hum.push(`${a.name} is defined by the zigzag ${zigzagHuman(D, a.src, c.steps)}: follow maps forwards, take preimages backwards.`);
      hum.push('Every element has an image:');
      hum.push(...em.human.map(t => '  ' + t), ...humStages.map(t => '  ' + t));
      hum.push('The image does not depend on the choices (0 relates only to 0):');
      hum.push(...emS.human.map(t => '  ' + t));
    } else {
      const defStmt = (dl) => constraintStmt(D, d, { lhs: c.lhs, rhs: c.rhs }, dl);
      if (c.how === 'direct') {
        rec.lean.push(`obtain ⟨${a.lean}, ${hdef}⟩ : ∃ ${a.lean} : ${T}, ${defStmt(a.lean)} := ⟨_, rfl⟩`);
        hum.push(`Take ${a.name} = ${humanComp(D, c.rhs)}.`);
      } else {
        const em = emitChase(ctx, r.run, c.how === 'mono' ? 'exists' : 'zero');
        if (c.how === 'mono') {
          rec.lean.push(`obtain ⟨${a.lean}, ${hdef}⟩ : ∃ ${a.lean} : ${T}, ${defStmt(a.lean)} := DC.factor_mono ${c.ref} ${L.compParen(D, c.rhs)} (fun ${r.run.x.name} => by`);
          rec.lean.push(...L.indentLines(em.lean, 2).map((l, n, arr) => (n === arr.length - 1 ? l + ')' : l)));
          hum.push(`${D.arrows[c.via].name} is injective, so ${a.name} exists (uniquely) with ${D.arrows[c.via].name}∘${a.name} = ${humanComp(D, c.rhs)} as soon as the image of ${humanComp(D, c.rhs)} lies in the image of ${D.arrows[c.via].name}:`);
        } else {
          rec.lean.push(`obtain ⟨${a.lean}, ${hdef}⟩ : ∃ ${a.lean} : ${T}, ${defStmt(a.lean)} := DC.factor_epi ${c.ref} ${L.compParen(D, c.rhs)} (fun ${r.run.w.name} ${r.run.hw} => by`);
          rec.lean.push(...L.indentLines(em.lean, 2).map((l, n, arr) => (n === arr.length - 1 ? l + ')' : l)));
          hum.push(`${D.arrows[c.via].name} is surjective, so ${a.name} exists (uniquely) with ${a.name}∘${D.arrows[c.via].name} = ${humanComp(D, c.rhs)} as soon as ${humanComp(D, c.rhs)} vanishes on the kernel of ${D.arrows[c.via].name}:`);
        }
        hum.push(...em.human.map(t => '  ' + t));
      }
      const dpt = ctx.names.numbered('d');
      rec.lean.push(`have ${dpt} : ∀ ${x}, ${L.applyLean(D, c.lhs, x)} = ${L.applyLean(D, c.rhs, x)} := fun ${x} => LinearMap.congr_fun ${hdef} ${x}`);
      defGens = [{ p: c.lhs, q: c.rhs, name: dpt }];
      rec.pathCons.push({ lhs: c.lhs, rhs: c.rhs, hname: hdef, pname: dpt });
      rec.conj.push({ stmt: defStmt, hname: hdef });
      rec.uniq = (hd) => (c.how === 'mono' ? `DC.mono_unique ${c.ref} (${hd}.trans ${hdef}.symm)`
        : c.how === 'epi' ? `DC.epi_unique ${c.ref} (${hd}.trans ${hdef}.symm)` : `${hd}.trans ${hdef}.symm`);
    }
    const phase2 = new Phase(D, Sd, G.concat(defGens), base.zgens);
    const cons = dashedConstraints(D, Sd, d);
    const others = c.how === 'zigzag' ? cons : cons.filter(k => pathKey(k.lhs) !== pathKey(c.lhs) || pathKey(k.rhs) !== pathKey(c.rhs));
    if (others.length) rec.lean.push(...ctx.emitRules(phase2, 0));
    for (const k of others) {
      const run = runChase(ctx, phase2, H, (chase) => {
        const u = introVar(chase, k.src);
        const vec = axpy(chase.push(chase.varVec(u), pathKey(k.lhs)), MINUS_ONE, chase.push(chase.varVec(u), pathKey(k.rhs)));
        return {
          goal: { kind: 'zero', obj: k.dst, vec }, factRefs: new Map(), u,
          introHuman: [[-1, `Let ${u.name} ∈ ${D.objs[k.src].name}; we show ${L.applyHuman(D, k.lhs, u.name)} = ${L.applyHuman(D, k.rhs, u.name)}.`]],
        };
      });
      const kstr = `${humanComp(D, k.lhs)} = ${humanComp(D, k.rhs)}`;
      if (run.res.status !== 'proved') {
        return {
          ok: false, arrow: d, status: run.res.status, run,
          reason: run.res.status === 'refuted'
            ? `${a.name} exists, but it does not make the diagram commute in general: ${kstr} fails.`
            : `Could not verify the commutativity ${kstr} for ${a.name}.`,
        };
      }
      const hn = ctx.names.fresh(`${hdef.replace(/₀$/, '')}${sub(rec.conj.length)}`);
      const em = emitChase(ctx, run, 'zero');
      rec.lean.push(`have ${hn} : ${L.compLean(D, k.lhs)} = ${L.compLean(D, k.rhs)} := by`);
      rec.lean.push(`  ext ${run.u.name}`);
      rec.lean.push('  rw [← sub_eq_zero]');
      rec.lean.push(...L.indentLines(em.lean, 2));
      const pn = ctx.names.numbered('d');
      rec.lean.push(`have ${pn} : ∀ ${x}, ${L.applyLean(D, k.lhs, x)} = ${L.applyLean(D, k.rhs, x)} := fun ${x} => LinearMap.congr_fun ${hn} ${x}`);
      rec.pathCons.push({ lhs: k.lhs, rhs: k.rhs, hname: hn, pname: pn });
      rec.conj.push({ stmt: (nm) => constraintStmt(D, d, k, nm), hname: hn });
      hum.push(`Commutativity ${kstr}:`);
      hum.push(...em.human.map(t => '  ' + t));
    }
    S = Sd;
    G = G.concat(rec.pathCons.map(k => ({ p: k.lhs, q: k.rhs, name: k.pname })));
    const phase3 = new Phase(D, S, G, base.zgens);
    rec.lean.push(...ctx.emitRules(phase3, 0));
    rec.human = [{ title, lines: hum }];
    records.push(rec);
  }
  return { ok: true, S, G, records };
}

function escapeRe(s) { return s.replace(/[.*+?^${}()|[\]\\]/g, '\\$&'); }
function humanComp(D, arr) { return arr.length ? arr.slice().reverse().map(i => D.arrows[i].name).join('∘') : 'id'; }

/** constraint statement with the dashed arrow's name replaced by `nm` */
function constraintStmt(D, d, k, nm) {
  const lhs = k.lhs.slice().reverse().map(i => (i === d ? nm : D.arrows[i].lean)).join(' ∘ₗ ');
  return `${lhs} = ${L.compLean(D, k.rhs)}`;
}

// ------------------------------------------------------------------ statement

function statement(ctx, H, base, conclusion, docLines) {
  const D = ctx.D;
  const out = [];
  out.push('/--');
  for (const l of docLines) out.push(l);
  out.push('-/');
  out.push('theorem diagram_chase {𝕜 : Type*} [Field 𝕜]');
  const mods = D.objs;
  const types = [...new Map(mods.map(o => [o.lean, o])).values()]; // modules identified by "=" share a type
  out.push(`    {${types.map(o => o.lean).join(' ')} : Type*}`);
  for (const o of types) {
    const inst = [`[AddCommGroup ${o.lean}]`, `[Module ${paren(L.RING)} ${o.lean}]`, `[Module.Finite ${paren(L.RING)} ${o.lean}]`];
    if (o.kind === 'free') inst.push(`[Module.Free ${paren(L.RING)} ${o.lean}]`);
    if (o.kind === 'zero') inst.push(`[Subsingleton ${o.lean}]`);
    out.push(`    ${inst.join(' ')}`);
  }
  for (const a of D.arrows) {
    if (a.dashed) continue;
    out.push(`    (${a.lean} : ${D.objs[a.src].lean} →ₗ[${L.RING}] ${D.objs[a.dst].lean})`);
  }
  for (const g of base.gens) out.push(`    (${g.stmtName} : ${L.compLean(D, g.p)} = ${L.compLean(D, g.q)})`);
  for (const [, h] of H.arrow) {
    if (h.stmt) out.push(`    (${h.name} : ${h.stmt})`);
    if (h.zeroName) out.push(`    (${h.zeroName} : ${h.zeroStmt})`);
  }
  for (const e of H.exact) out.push(`    (${e.ref} : Function.Exact ${D.arrows[e.first].lean} ${D.arrows[e.second].lean})`);
  for (const p of H.pb) out.push(`    (${p.ref} : DC.IsPB ${[p.sq.a1, p.sq.a2, p.sq.b1, p.sq.b2].map(i => D.arrows[i].lean).join(' ')})`);
  for (const p of H.po) out.push(`    (${p.ref} : DC.IsPO ${[p.sq.a1, p.sq.a2, p.sq.b1, p.sq.b2].map(i => D.arrows[i].lean).join(' ')})`);
  out.push(`    : ${conclusion} := by`);
  return out;
}

const paren = (s) => (/\s/.test(s) ? `(${s})` : s);

function preambleLines(ctx, H, base) {
  const D = ctx.D, x = ctx.binder;
  const out = [];
  if (base.gens.length) out.push('-- commutativity, pointwise');
  for (const g of base.gens) {
    out.push(`have ${g.name} : ∀ ${x}, ${L.applyLean(D, g.p, x)} = ${L.applyLean(D, g.q, x)} := fun ${x} => LinearMap.congr_fun ${g.stmtName} ${x}`);
  }
  if (base.zgens.length) out.push('-- vanishing composites');
  for (const z of base.zgens) {
    const lhs = L.applyLean(D, z.w, x);
    let pf;
    const src = z.source;
    if (src.type === 'exact') pf = `${H.exact[src.index].ref}.apply_apply_eq_zero`;
    else if (src.type === 'zeroMap') pf = `fun ${x} => LinearMap.congr_fun ${H.arrow.get(src.arrow).zeroName} ${x}`;
    else if (src.type === 'intoZero') pf = `fun ${x} => Subsingleton.elim _ _`;
    else pf = `DC.map_from_zero ${D.arrows[src.arrow].lean}`;
    out.push(`have ${z.name} : ∀ ${x}, ${lhs} = 0 := ${pf}`);
  }
  return out;
}

// ------------------------------------------------------------------ queries

export function describeQuery(D, q) {
  const P = (arr) => humanComp(D, arr);
  const S = (s) => (s.kind === 'ker' ? `ker ${P(s.path)}` : s.kind === 'im' ? `im ${P(s.path)}` : s.kind === 'zero' ? '0' : D.objs[s.obj].name);
  switch (q.type) {
    case 'injective': return `${P(q.path)} is injective`;
    case 'surjective': return `${P(q.path)} is surjective`;
    case 'iso': return `${P(q.path)} is an isomorphism`;
    case 'zero': return `${P(q.path)} = 0`;
    case 'exact': return `${P(q.first)}, ${P(q.second)} is exact at ${D.objs[D.arrows[q.first[q.first.length - 1]].dst].name}`;
    case 'subset': return `${S(q.lhs)} ⊆ ${S(q.rhs)}`;
    case 'equal': return `${S(q.lhs)} = ${S(q.rhs)}`;
    case 'existsMap': return `there is ${{ injective: 'an injective', surjective: 'a surjective', iso: 'an isomorphism' }[q.prop]} map ${D.objs[q.from].name} → ${D.objs[q.to].name}`;
    case 'induced': return `the induced map ${D.arrows[q.arrow].name} exists (uniquely) and makes the diagram commute`;
    default: return '?';
  }
}

function normalizeQuery(D, query) {
  const idx = (id) => {
    const i = D.arrowIndex.get(id);
    if (i === undefined) throw new Error('Query refers to a deleted map.');
    return i;
  };
  const path = (ids) => {
    if (!ids || !ids.length) throw new Error('Choose a map.');
    const arr = ids.map(idx);
    for (let n = 1; n < arr.length; n++) if (D.arrows[arr[n - 1]].dst !== D.arrows[arr[n]].src) throw new Error('The chosen maps are not composable.');
    return arr;
  };
  const q = { type: query.type };
  const sub = (s) => {
    const r = { kind: s.kind };
    if (s.kind === 'ker' || s.kind === 'im') r.path = path(s.path);
    else { r.obj = D.objIndex.get(s.module); if (r.obj === undefined) throw new Error('Choose a module.'); }
    return r;
  };
  switch (query.type) {
    case 'injective': case 'surjective': case 'iso': case 'zero': q.path = path(query.path); break;
    case 'exact':
      q.first = path(query.first); q.second = path(query.second);
      if (D.arrows[q.first[q.first.length - 1]].dst !== D.arrows[q.second[0]].src) throw new Error('The two maps are not composable.');
      break;
    case 'subset': case 'equal': {
      q.lhs = sub(query.lhs); q.rhs = sub(query.rhs);
      const amb = (s) => s.kind === 'ker' ? D.arrows[s.path[0]].src : s.kind === 'im' ? D.arrows[s.path[s.path.length - 1]].dst : s.obj;
      if (amb(q.lhs) !== amb(q.rhs)) throw new Error('Both sides must be submodules of the same module.');
      q.ambient = amb(q.lhs);
      break;
    }
    case 'existsMap':
      q.from = D.objIndex.get(query.from); q.to = D.objIndex.get(query.to); q.prop = query.prop;
      if (q.from === undefined || q.to === undefined) throw new Error('Choose two modules.');
      break;
    case 'induced': q.arrow = idx(query.arrow); if (!D.arrows[q.arrow].dashed) throw new Error('Mark the map as induced (∃!, dashed) first.'); break;
    default: throw new Error('Unknown query type.');
  }
  return q;
}

function queryPaths(q) {
  switch (q.type) {
    case 'injective': case 'surjective': case 'iso': case 'zero': return [q.path];
    case 'exact': return [q.first, q.second];
    case 'subset': case 'equal': return [q.lhs.path, q.rhs.path].filter(Boolean);
    case 'induced': return [[q.arrow]];
    default: return [];
  }
}

// ------------------------------------------------------------------ main

export function prove(diagram, query, opts = {}) {
  opts = { maxRounds: 10, maxVars: 60, ...opts };
  let D;
  try {
    D = compile(diagram);
  } catch (e) { return { status: 'error', message: e.message }; }
  if (D.errors.length) return { status: 'error', message: D.errors.join('\n') };
  let q;
  try { q = normalizeQuery(D, query); } catch (e) { return { status: 'error', message: e.message }; }
  const names = new Names(D.usedLean);
  const ctx = new Ctx(D, names, opts);
  const H = assignHyps(D, names);
  const solid = new Set(D.arrows.filter(a => !a.dashed).map(a => a.i));
  const zgens = baseZeroGens(D, solid);
  zgens.forEach(z => { z.name = names.numbered('z'); });
  const gens = baseGenerators(D, solid, zgens);
  gens.forEach(g => { g.stmtName = names.numbered('hc'); g.name = names.numbered('c'); });
  const base = { solid, zgens, gens };
  const basePhase = new Phase(D, solid, gens, zgens);
  const title = describeQuery(D, q);
  const out = { status: 'proved', title, blocks: [], D };

  try {
    // existsMap: choose the path now (solid part + dashed if needed)
    if (q.type === 'existsMap') {
      const p = minPath(D, basePhase, q.from, q.to);
      if (!p) {
        const pd = minPath(D, new Phase(D, new Set(D.arrows.map(a => a.i)), [], []), q.from, q.to);
        if (!pd) return { status: 'unknown', title, message: `There is no map ${D.objs[q.from].name} → ${D.objs[q.to].name} in the diagram to test. Draw one (possibly a dashed induced map) and query its properties.` };
        q.path = pd;
      } else q.path = p;
    }
    const dashedUsed = new Set();
    for (const p of queryPaths(q).concat(q.path ? [q.path] : [])) for (const i of p) if (D.arrows[i].dashed) dashedUsed.add(i);

    const leanBody = [];
    leanBody.push(...L.indentLines(preambleLines(ctx, H, base), 2));
    const baseRules = ctx.emitRules(basePhase, 2);
    if (baseRules.length) { leanBody.push('  -- rewrite rules to normal forms of paths'); leanBody.push(...baseRules); }

    const dash = constructDashed(ctx, H, base, dashedUsed);
    if (!dash.ok) {
      const res = { status: dash.status || 'unknown', title, message: dash.reason };
      if (dash.run && dash.run.res.status === 'refuted') res.counterexample = renderCounterexample(ctx, dash.run);
      return res;
    }
    for (const r of dash.records) {
      leanBody.push(...L.indentLines(r.lean, 2));
      out.blocks.push(...r.human);
    }
    const phase = new Phase(D, dash.S, dash.G, zgens);
    if (dash.records.length) leanBody.push(...ctx.emitRules(phase, 2));

    // conclusion + goal proof
    const g = goalProof(ctx, H, phase, q);
    if (g.status !== 'proved') {
      const res = { status: g.status, title, message: g.message };
      if (g.run && g.run.res.status === 'refuted') res.counterexample = renderCounterexample(ctx, g.run);
      return res;
    }
    out.blocks.push(...g.human);
    // wrap conclusion with dashed-arrow existentials
    let concl = g.conclusion;
    let refineLines = [];
    for (let n = dash.records.length - 1; n >= 0; n--) {
      const r = dash.records[n];
      const a = D.arrows[r.arrow];
      const T = `${D.objs[a.src].lean} →ₗ[${L.RING}] ${D.objs[a.dst].lean}`;
      const other = names.fresh(safeSuffix(a.name) ? `${a.name}'` : 'd\'');
      const conj = (nm) => r.conj.map(k => k.stmt(nm)).join(' ∧ ');
      const conjParen = (nm) => (r.conj.length > 1 ? `(${conj(nm)})` : conj(nm));
      const isLastInduced = q.type === 'induced' && r.arrow === q.arrow && n === dash.records.length - 1;
      if (isLastInduced) {
        concl = `∃! ${a.lean} : ${T}, ${conj(a.lean)}`;
      } else {
        concl = `∃ ${a.lean} : ${T}, ${conjParen(a.lean)} ∧ (∀ ${other} : ${T}, ${conj(other)} → ${other} = ${a.lean}) ∧\n      ${concl}`;
      }
      const hd = r.conj.length > 1 ? 'hh.1' : 'hh';
      const uniq = r.uniq(hd);
      const tuple = r.conj.length > 1 ? `⟨${r.conj.map(k => k.hname).join(', ')}⟩` : r.conj[0].hname;
      if (isLastInduced) refineLines.unshift(`exact ⟨${a.lean}, ${tuple}, fun ${other} hh => ${uniq}⟩`);
      else refineLines.unshift(`refine ⟨${a.lean}, ${tuple}, fun ${other} hh => ${uniq}, ?_⟩`);
    }
    leanBody.push(...L.indentLines(refineLines, 2));
    leanBody.push(...L.indentLines(g.lean, 2));

    const doc = [
      `Diagram chase over k[t] (k = 𝕜 a field). All modules finitely generated; the diagram commutes.`,
      ...D.objs.filter(o => o.construct).map(o => {
        const f = D.arrows[D.arrowIndex.get(o.construct.arrow)];
        return `* ${o.name} is the ${{ ker: 'kernel', im: 'image', coker: 'cokernel' }[o.construct.type]} of ${f ? f.name : '?'}, encoded by its universal maps.`;
      }),
      ...D.arrows.filter(a => a.equal).map(a => `* ${D.objs[a.src].name} = ${D.objs[a.dst].name}: the same module, and ${a.name} is its identity map.`),
      `Claim: ${title}.`,
    ];
    const stmt = statement(ctx, H, base, concl, doc);
    out.leanTheorem = `${stmt.join('\n')}\n${leanBody.join('\n')}\n`;
    out.lean = `${L.PRELUDE}\n${out.leanTheorem}`;
    return out;
  } catch (e) {
    return { status: 'error', title, message: `Internal error: ${e.message}`, stack: e.stack };
  }
}

/** build conclusion + proof for the (final-phase) query */
function goalProof(ctx, H, phase, q) {
  const D = ctx.D;
  const comp = (p) => L.compParen(D, p);
  const compNP = (p) => L.compLean(D, p);
  const human = [];
  const fail = (run, what) => ({
    status: run.res.status === 'refuted' ? 'refuted' : 'unknown', run,
    message: run.res.status === 'refuted' ? `False in general: ${what}. The chase saturated; the finite-dimensional model below is a counterexample.` : `Could not decide ${what} within the search budget.`,
  });

  const injective = (p, label) => {
    const X = D.arrows[p[0]].src;
    let hx;
    const run = runChase(ctx, phase, H, (chase) => {
      const x = introVar(chase, X);
      hx = ctx.names.fresh('hx');
      const f = chase.addFact(chase.vecObj(chase.push(chase.varVec(x), pathKey(p)), D.arrows[p[p.length - 1]].dst), chase.push(chase.varVec(x), pathKey(p)), { how: 'intro', step: -1 });
      return { goal: { kind: 'zero', obj: X, vec: chase.varVec(x) }, factRefs: new Map([[f.id, hx]]), x, introHuman: [[f.id, `Let ${x.name} ∈ ${D.objs[X].name} with ${L.applyHuman(D, p, x.name)} = 0 {n}.`]] };
    });
    if (run.res.status !== 'proved') return fail(run, `${label || humanComp(D, p)} is injective`);
    const em = emitChase(ctx, run, 'zero');
    return {
      status: 'proved',
      lean: [`refine (injective_iff_map_eq_zero ${comp(p)}).mpr ?_`, `intro ${run.x.name} ${hx}`, ...em.lean],
      human: [{ title: `${label || humanComp(D, p)} is injective`, lines: em.human }],
    };
  };
  const surjective = (p, label) => {
    const Y = D.arrows[p[p.length - 1]].dst, X = D.arrows[p[0]].src;
    const run = runChase(ctx, phase, H, (chase) => {
      const y = introVar(chase, Y);
      return { goal: { kind: 'image', obj: Y, vec: chase.varVec(y), src: X, path: pathKey(p) }, factRefs: new Map(), y, pathHuman: humanComp(D, p), introHuman: [[-1, `Let ${y.name} ∈ ${D.objs[Y].name}.`]] };
    });
    if (run.res.status !== 'proved') return fail(run, `${label || humanComp(D, p)} is surjective`);
    const em = emitChase(ctx, run, 'exists');
    return {
      status: 'proved', lean: [`intro ${run.y.name}`, ...em.lean],
      human: [{ title: `${label || humanComp(D, p)} is surjective`, lines: em.human }],
    };
  };
  const bullets = (a, b) => [...bullet(a), ...bullet(b)];

  switch (q.type) {
    case 'injective': { const r = injective(q.path); return { ...r, conclusion: `Function.Injective ${comp(q.path)}` }; }
    case 'surjective': { const r = surjective(q.path); return { ...r, conclusion: `Function.Surjective ${comp(q.path)}` }; }
    case 'iso': {
      const a = injective(q.path); if (a.status !== 'proved') return a;
      const b = surjective(q.path); if (b.status !== 'proved') return b;
      return { status: 'proved', conclusion: `Function.Bijective ${comp(q.path)}`, lean: ['refine ⟨?_, ?_⟩', ...bullets(a.lean, b.lean)], human: [...a.human, ...b.human] };
    }
    case 'zero': {
      const p = q.path;
      const X = D.arrows[p[0]].src, Y = D.arrows[p[p.length - 1]].dst;
      const run = runChase(ctx, phase, H, (chase) => {
        const x = introVar(chase, X);
        return { goal: { kind: 'zero', obj: Y, vec: chase.push(chase.varVec(x), pathKey(p)) }, factRefs: new Map(), x, introHuman: [[-1, `Let ${x.name} ∈ ${D.objs[X].name}.`]] };
      });
      if (run.res.status !== 'proved') return fail(run, `${humanComp(D, p)} = 0`);
      const em = emitChase(ctx, run, 'zero');
      return { status: 'proved', conclusion: `${compNP(p)} = 0`, lean: [`ext ${run.x.name}`, ...em.lean], human: [{ title: `${humanComp(D, p)} = 0`, lines: em.human }] };
    }
    case 'exact': {
      const p1 = q.first, p2 = q.second;
      const A = D.arrows[p1[0]].src, B = D.arrows[p2[0]].src;
      let hy;
      const run1 = runChase(ctx, phase, H, (chase) => {
        const y = introVar(chase, B);
        hy = ctx.names.fresh('hy');
        const img = chase.push(chase.varVec(y), pathKey(p2));
        const f = chase.addFact(chase.vecObj(img, D.arrows[p2[p2.length - 1]].dst), img, { how: 'intro', step: -1 });
        return { goal: { kind: 'image', obj: B, vec: chase.varVec(y), src: A, path: pathKey(p1) }, factRefs: new Map([[f.id, hy]]), y, pathHuman: humanComp(D, p1), introHuman: [[f.id, `Let ${y.name} ∈ ${D.objs[B].name} with ${L.applyHuman(D, p2, y.name)} = 0 {n}.`]] };
      });
      if (run1.res.status !== 'proved') return fail(run1, `ker ${humanComp(D, p2)} ⊆ im ${humanComp(D, p1)}`);
      const em1 = emitChase(ctx, run1, 'exists');
      const run2 = runChase(ctx, phase, H, (chase) => {
        const x = introVar(chase, A);
        return { goal: { kind: 'zero', obj: D.arrows[p2[p2.length - 1]].dst, vec: chase.push(chase.varVec(x), pathKey(p1.concat(p2))) }, factRefs: new Map(), x, introHuman: [[-1, `Let ${x.name} ∈ ${D.objs[A].name}.`]] };
      });
      if (run2.res.status !== 'proved') return fail(run2, `${humanComp(D, p2)}∘${humanComp(D, p1)} = 0`);
      const em2 = emitChase(ctx, run2, 'zero');
      return {
        status: 'proved', conclusion: `Function.Exact ${comp(p1)} ${comp(p2)}`,
        lean: [`intro ${run1.y.name}`, 'constructor', ...bullet([`intro ${hy}`, ...em1.lean]), ...bullet([`rintro ⟨${run2.x.name}, rfl⟩`, ...em2.lean])],
        human: [{ title: `ker ${humanComp(D, p2)} ⊆ im ${humanComp(D, p1)}`, lines: em1.human }, { title: `im ${humanComp(D, p1)} ⊆ ker ${humanComp(D, p2)}`, lines: em2.human }],
      };
    }
    case 'subset': case 'equal': {
      const one = (S, T) => subsetProof(ctx, H, phase, q.ambient, S, T, fail);
      const smod = (s) => s.kind === 'ker' ? `LinearMap.ker ${comp(s.path)}` : s.kind === 'im' ? `LinearMap.range ${comp(s.path)}` : s.kind === 'zero' ? `(⊥ : Submodule ${paren(L.RING)} ${D.objs[q.ambient].lean})` : `(⊤ : Submodule ${paren(L.RING)} ${D.objs[q.ambient].lean})`;
      if (q.type === 'subset') {
        const r = one(q.lhs, q.rhs);
        if (r.status !== 'proved') return r;
        return { ...r, conclusion: `${smod(q.lhs)} ≤ ${smod(q.rhs)}` };
      }
      const a = one(q.lhs, q.rhs); if (a.status !== 'proved') return a;
      const b = one(q.rhs, q.lhs); if (b.status !== 'proved') return b;
      return { status: 'proved', conclusion: `${smod(q.lhs)} = ${smod(q.rhs)}`, lean: ['apply le_antisymm', ...bullets(a.lean, b.lean)], human: [...a.human, ...b.human] };
    }
    case 'existsMap': {
      const p = q.path;
      const T = `${D.objs[q.from].lean} →ₗ[${L.RING}] ${D.objs[q.to].lean}`;
      const nm = ctx.names.fresh('φ');
      const label = `${humanComp(D, p)} : ${D.objs[q.from].name} → ${D.objs[q.to].name}`;
      if (q.prop === 'injective') {
        const r = injective(p, label); if (r.status !== 'proved') return r;
        return { ...r, conclusion: `∃ ${nm} : ${T}, Function.Injective ${nm}`, lean: [`refine ⟨${compNP(p)}, ?_⟩`, ...r.lean] };
      }
      if (q.prop === 'surjective') {
        const r = surjective(p, label); if (r.status !== 'proved') return r;
        return { ...r, conclusion: `∃ ${nm} : ${T}, Function.Surjective ${nm}`, lean: [`refine ⟨${compNP(p)}, ?_⟩`, ...r.lean] };
      }
      const a = injective(p, label); if (a.status !== 'proved') return a;
      const b = surjective(p, label); if (b.status !== 'proved') return b;
      return { status: 'proved', conclusion: `∃ ${nm} : ${T}, Function.Bijective ${nm}`, lean: [`refine ⟨${compNP(p)}, ?_, ?_⟩`, ...bullets(a.lean, b.lean)], human: [...a.human, ...b.human] };
    }
    case 'induced':
      return { status: 'proved', conclusion: 'True', lean: [], human: [] };
    default:
      return { status: 'error', message: 'unknown query' };
  }
}

function bullet(lines) {
  return L.flat(lines).map((l, n) => (n === 0 ? `· ${l}` : `  ${l}`));
}

function subsetProof(ctx, H, phase, amb, S, T, fail) {
  const D = ctx.D;
  const comp = (p) => L.compParen(D, p);
  const label = (s) => ({ ker: `ker ${humanComp(D, s.path || [])}`, im: `im ${humanComp(D, s.path || [])}`, zero: '0', all: D.objs[amb].name }[s.kind]);
  const title = `${label(S)} ⊆ ${label(T)}`;
  if (S.kind === 'zero') return { status: 'proved', lean: ['exact bot_le'], human: [{ title, lines: ['0 is contained in every submodule.'] }] };
  if (T.kind === 'all') return { status: 'proved', lean: ['exact le_top'], human: [{ title, lines: ['Every submodule is contained in the whole module.'] }] };
  const v = ctx.names.fresh('v'), hv = ctx.names.fresh('hv');
  const intro = [`intro ${v} ${hv}`];
  let elemName = v;
  const run = runChase(ctx, phase, H, (chase) => {
    let elem, factRefs = new Map(), introHuman = [];
    if (S.kind === 'ker') {
      const x = chase.newVar(amb, null, -1);
      x.name = v; // reuse the Lean binder name
      const img = chase.push(chase.varVec(x), pathKey(S.path));
      const f = chase.addFact(chase.vecObj(img, D.arrows[S.path[S.path.length - 1]].dst), img, { how: 'intro', step: -1 });
      factRefs.set(f.id, hv);
      intro.push(`rw [LinearMap.mem_ker] at ${hv}`);
      elem = chase.varVec(x);
      introHuman.push([f.id, `Let ${v} ∈ ${D.objs[amb].name} with ${L.applyHuman(D, S.path, v)} = 0 {n}.`]);
    } else if (S.kind === 'im') {
      const src = D.arrows[S.path[0]].src;
      const a = chase.newVar(src, null, -1);
      intro.push(`obtain ⟨${a.name}, rfl⟩ := LinearMap.mem_range.mp ${hv}`);
      elem = chase.push(chase.varVec(a), pathKey(S.path));
      elemName = L.applyHuman(D, S.path, a.name);
      introHuman.push([-1, `Let ${a.name} ∈ ${D.objs[src].name}; consider ${elemName}.`]);
    } else { // all
      const x = chase.newVar(amb, null, -1);
      x.name = v;
      elem = chase.varVec(x);
      introHuman.push([-1, `Let ${v} ∈ ${D.objs[amb].name}.`]);
    }
    let goal, finish;
    if (T.kind === 'ker') {
      goal = { kind: 'zero', obj: D.arrows[T.path[T.path.length - 1]].dst, vec: chase.push(elem, pathKey(T.path)) };
      finish = 'zero';
    } else if (T.kind === 'im') {
      goal = { kind: 'image', obj: amb, vec: elem, src: D.arrows[T.path[0]].src, path: pathKey(T.path) };
      finish = 'memRange';
    } else { // zero
      goal = { kind: 'zero', obj: amb, vec: elem };
      finish = 'zero';
    }
    return { goal, factRefs, introHuman, finish, pathHuman: T.path ? humanComp(D, T.path) : '' };
  });
  if (run.res.status !== 'proved') return fail(run, title);
  if (T.kind === 'ker') intro.push('rw [LinearMap.mem_ker]');
  if (T.kind === 'zero') intro.push('rw [Submodule.mem_bot]');
  const em = emitChase(ctx, run, run.finish);
  return { status: 'proved', lean: [...intro, ...em.lean], human: [{ title, lines: em.human }] };
}
