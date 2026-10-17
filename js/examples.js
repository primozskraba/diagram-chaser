// Built-in example diagrams (also used by the test-suite).
import { emptyDiagram, addModule, addArrow, addExactChain, addConstruction, addSquare, arrowById } from './model.js';

function build(spec) {
  const d = emptyDiagram();
  const mid = new Map(), aid = new Map();
  for (const [name, x, y, kind, key = name] of spec.modules) {
    const m = addModule(d, { name, x, y, kind: kind || 'general', id: `m_${key}` });
    mid.set(key, m.id);
  }
  for (const [name, s, t, props = ''] of spec.arrows) {
    const a = addArrow(d, {
      name, src: mid.get(s), dst: mid.get(t), id: `a_${name}`,
      mono: /mono|iso/.test(props), epi: /epi|iso/.test(props), zero: /zero/.test(props), dashed: /dashed/.test(props),
      equal: /equal/.test(props),
    });
    aid.set(name, a.id);
  }
  for (const chain of spec.exact || []) addExactChain(d, chain.map(n => aid.get(n)));
  for (const [type, a1, a2, b1, b2] of spec.squares || []) {
    addSquare(d, type, { a1: aid.get(a1), a2: aid.get(a2), b1: aid.get(b1), b2: aid.get(b2) });
  }
  for (const [type, f] of spec.constructions || []) {
    const M = addConstruction(d, type, aid.get(f) || d.arrows.find(x => x.name === f).id);
    if (spec.place && spec.place[M.name]) Object.assign(M, spec.place[M.name]);
  }
  for (const [name, s, t, props = '', extra = {}] of spec.later || []) {
    const find = (n) => (mid.get(n) || d.modules.find(m => m.name === n).id);
    const a = addArrow(d, { name, src: find(s), dst: find(t), id: `a_${name}`, dashed: /dashed/.test(props), mono: /mono/.test(props), epi: /epi/.test(props), ...extra });
    aid.set(name, a.id);
  }
  const A = (n) => aid.get(n) || d.arrows.find(a => a.name === n).id;
  const M = (n) => mid.get(n) || d.modules.find(m => m.name === n).id;
  const queries = (spec.queries || []).map(q => q({ A, M }));
  return { diagram: d, queries };
}

export const EXAMPLES = [
  {
    id: 'five',
    title: 'Five lemma',
    blurb: 'Rows exact, β and δ isomorphisms, α surjective, ε injective ⇒ γ is an isomorphism.',
    make: () => build({
      modules: [['A', 0, 0], ['B', 1, 0], ['C', 2, 0], ['D', 3, 0], ['E', 4, 0],
        ["A'", 0, 1], ["B'", 1, 1], ["C'", 2, 1], ["D'", 3, 1], ["E'", 4, 1]],
      arrows: [['f', 'A', 'B'], ['g', 'B', 'C'], ['h', 'C', 'D'], ['j', 'D', 'E'],
        ["f'", "A'", "B'"], ["g'", "B'", "C'"], ["h'", "C'", "D'"], ["j'", "D'", "E'"],
        ['α', 'A', "A'", 'epi'], ['β', 'B', "B'", 'iso'], ['γ', 'C', "C'"], ['δ', 'D', "D'", 'iso'], ['ε', 'E', "E'", 'mono']],
      exact: [['f', 'g', 'h', 'j'], ["f'", "g'", "h'", "j'"]],
      queries: [({ A }) => ({ type: 'iso', path: [A('γ')] }), ({ A }) => ({ type: 'injective', path: [A('γ')] })],
    }),
  },
  {
    id: 'four-mono',
    title: 'Four lemma (mono)',
    blurb: 'Drop the hypothesis on α and γ is no longer injective: the chaser finds a counterexample.',
    make: () => build({
      modules: [['A', 0, 0], ['B', 1, 0], ['C', 2, 0], ['D', 3, 0],
        ["A'", 0, 1], ["B'", 1, 1], ["C'", 2, 1], ["D'", 3, 1]],
      arrows: [['f', 'A', 'B'], ['g', 'B', 'C'], ['h', 'C', 'D'],
        ["f'", "A'", "B'"], ["g'", "B'", "C'"], ["h'", "C'", "D'"],
        ['α', 'A', "A'"], ['β', 'B', "B'", 'mono'], ['γ', 'C', "C'"], ['δ', 'D', "D'", 'mono']],
      exact: [['f', 'g', 'h'], ["f'", "g'", "h'"]],
      queries: [({ A }) => ({ type: 'injective', path: [A('γ')] })],
    }),
  },
  {
    id: 'kernels',
    title: 'Kernel sequence (snake, first half)',
    blurb: 'Exact rows 0 → A → B → C and 0 → A′ → B′ → C′; the induced maps on kernels form an exact sequence.',
    make: () => build({
      modules: [['0', 0, 1, 'zero'], ['A', 1, 1], ['B', 2, 1], ['C', 3, 1],
        ["0'", 0, 2, 'zero'], ["A'", 1, 2], ["B'", 2, 2], ["C'", 3, 2]],
      arrows: [['z', '0', 'A'], ['f', 'A', 'B'], ['g', 'B', 'C'],
        ["z'", "0'", "A'"], ["f'", "A'", "B'"], ["g'", "B'", "C'"],
        ['a', 'A', "A'"], ['b', 'B', "B'"], ['c', 'C', "C'"]],
      exact: [['z', 'f', 'g'], ["z'", "f'", "g'"]],
      constructions: [['ker', 'a'], ['ker', 'b'], ['ker', 'c']],
      place: { 'ker a': { x: 1, y: 0 }, 'ker b': { x: 2, y: 0 }, 'ker c': { x: 3, y: 0 } },
      later: [['κ', 'ker a', 'ker b', 'dashed'], ['λ', 'ker b', 'ker c', 'dashed']],
      queries: [({ A }) => ({ type: 'exact', first: [A('κ')], second: [A('λ')] }), ({ A }) => ({ type: 'injective', path: [A('κ')] })],
    }),
  },
  {
    id: 'cokernels',
    title: 'Cokernel sequence (snake, second half)',
    blurb: 'Exact rows A → B → C → 0 and A′ → B′ → C′ → 0; the induced maps on cokernels form an exact sequence.',
    make: () => build({
      modules: [['A', 0, 0], ['B', 1, 0], ['C', 2, 0], ['0', 3, 0, 'zero'],
        ["A'", 0, 1], ["B'", 1, 1], ["C'", 2, 1], ["0'", 3, 1, 'zero']],
      arrows: [['f', 'A', 'B'], ['g', 'B', 'C'], ['z', 'C', '0'],
        ["f'", "A'", "B'"], ["g'", "B'", "C'"], ["z'", "C'", "0'"],
        ['a', 'A', "A'"], ['b', 'B', "B'"], ['c', 'C', "C'"]],
      exact: [['f', 'g', 'z'], ["f'", "g'", "z'"]],
      constructions: [['coker', 'a'], ['coker', 'b'], ['coker', 'c']],
      place: { 'coker a': { x: 0, y: 2 }, 'coker b': { x: 1, y: 2 }, 'coker c': { x: 2, y: 2 } },
      later: [['κ', 'coker a', 'coker b', 'dashed'], ['λ', 'coker b', 'coker c', 'dashed']],
      queries: [({ A }) => ({ type: 'exact', first: [A('κ')], second: [A('λ')] }), ({ A }) => ({ type: 'surjective', path: [A('λ')] })],
    }),
  },
  {
    id: 'snake',
    title: 'Snake lemma',
    blurb: 'Exact rows A → B → C → 0 and 0 → A′ → B′ → C′. The connecting map δ: ker γ → coker α is found as a zigzag through the diagram, and ker β → ker γ → coker α → coker β is exact.',
    make: () => build({
      modules: [['A', 1, 2], ['B', 2, 2], ['C', 3, 2], ['0', 4, 2, 'zero'],
        ["0'", 0, 3, 'zero'], ["A'", 1, 3], ["B'", 2, 3], ["C'", 3, 3]],
      arrows: [['f', 'A', 'B'], ['g', 'B', 'C'], ['z', 'C', '0'],
        ["z'", "0'", "A'"], ["f'", "A'", "B'"], ["g'", "B'", "C'"],
        ['α', 'A', "A'"], ['β', 'B', "B'"], ['γ', 'C', "C'"]],
      exact: [['f', 'g', 'z'], ["z'", "f'", "g'"]],
      constructions: [['ker', 'β'], ['ker', 'γ'], ['coker', 'α'], ['coker', 'β']],
      place: { 'ker β': { x: 2, y: 1 }, 'ker γ': { x: 3, y: 1 }, 'coker α': { x: 2, y: 4 }, 'coker β': { x: 3, y: 4 } },
      later: [['λ', 'ker β', 'ker γ', 'dashed'], ['δ', 'ker γ', 'coker α', 'dashed', { bend: -1 }], ['κ', 'coker α', 'coker β', 'dashed']],
      queries: [
        ({ A }) => ({ type: 'exact', first: [A('λ')], second: [A('δ')] }),
        ({ A }) => ({ type: 'exact', first: [A('δ')], second: [A('κ')] }),
        ({ A }) => ({ type: 'induced', arrow: A('δ') }),
      ],
    }),
  },
  {
    id: 'retract',
    title: 'Retract (r∘i = id)',
    blurb: 'i : A → B and r : B → A with r∘i = id, drawn with an “=” map: both A’s are the same module and the map is its identity. Then i is injective, r is surjective, and ker r ≅ coker i.',
    make: () => build({
      modules: [['A', 0, 1], ['B', 1, 0], ['A', 2, 1, 'general', 'A2']],
      arrows: [['i', 'A', 'B'], ['r', 'B', 'A2'], ['id_A', 'A', 'A2', 'equal']],
      constructions: [['ker', 'r'], ['coker', 'i']],
      place: { 'ker r': { x: 0, y: 0 }, 'coker i': { x: 2, y: 0 } },
      queries: [
        ({ A }) => ({ type: 'injective', path: [A('i')] }),
        ({ A }) => ({ type: 'surjective', path: [A('r')] }),
        ({ A }) => ({ type: 'iso', path: [A('ι_r'), A('π_i')] }),
      ],
    }),
  },
  {
    id: 'pullback',
    title: 'Pullback of a mono',
    blurb: 'In a pullback square, the map opposite an injective map is injective.',
    make: () => build({
      modules: [['P', 0, 0], ['A', 1, 0], ['B', 0, 1], ['C', 1, 1]],
      arrows: [['p', 'P', 'A'], ['q', 'P', 'B'], ['f', 'A', 'C'], ['g', 'B', 'C', 'mono']],
      squares: [['pullback', 'p', 'q', 'f', 'g']],
      queries: [({ A }) => ({ type: 'injective', path: [A('p')] })],
    }),
  },
  {
    id: 'pushout',
    title: 'Pushout of an epi',
    blurb: 'In a pushout square, the map opposite a surjective map is surjective.',
    make: () => build({
      modules: [['A', 0, 0], ['B', 1, 0], ['C', 0, 1], ['Q', 1, 1]],
      arrows: [['f', 'A', 'B', 'epi'], ['g', 'A', 'C'], ['u', 'B', 'Q'], ['v', 'C', 'Q']],
      squares: [['pushout', 'f', 'g', 'u', 'v']],
      queries: [({ A }) => ({ type: 'surjective', path: [A('v')] })],
    }),
  },
  {
    id: 'subobjects',
    title: 'Kernels and images of composites',
    blurb: 'ker f ⊆ ker g∘f and im g∘f ⊆ im g hold always; the converses need hypotheses.',
    make: () => build({
      modules: [['A', 0, 0], ['B', 1, 0], ['C', 2, 0]],
      arrows: [['f', 'A', 'B'], ['g', 'B', 'C']],
      queries: [
        ({ A }) => ({ type: 'subset', lhs: { kind: 'ker', path: [A('f')] }, rhs: { kind: 'ker', path: [A('f'), A('g')] } }),
        ({ A }) => ({ type: 'subset', lhs: { kind: 'im', path: [A('f'), A('g')] }, rhs: { kind: 'im', path: [A('g')] } }),
        ({ A }) => ({ type: 'subset', lhs: { kind: 'ker', path: [A('f'), A('g')] }, rhs: { kind: 'ker', path: [A('f')] } }),
      ],
    }),
  },
  {
    id: 'nine',
    title: '3×3 lemma',
    blurb: 'Columns and the bottom two rows short exact (↪, ↠, exact in the middle) ⇒ the top row is short exact.',
    make: () => build({
      modules: [['A₁', 0, 0], ['A₂', 1, 0], ['A₃', 2, 0], ['B₁', 0, 1], ['B₂', 1, 1], ['B₃', 2, 1], ['C₁', 0, 2], ['C₂', 1, 2], ['C₃', 2, 2]],
      arrows: [['f₁', 'A₁', 'A₂'], ['g₁', 'A₂', 'A₃'],
        ['f₂', 'B₁', 'B₂', 'mono'], ['g₂', 'B₂', 'B₃', 'epi'],
        ['f₃', 'C₁', 'C₂', 'mono'], ['g₃', 'C₂', 'C₃', 'epi'],
        ['u₁', 'A₁', 'B₁', 'mono'], ['v₁', 'B₁', 'C₁', 'epi'],
        ['u₂', 'A₂', 'B₂', 'mono'], ['v₂', 'B₂', 'C₂', 'epi'],
        ['u₃', 'A₃', 'B₃', 'mono'], ['v₃', 'B₃', 'C₃', 'epi']],
      exact: [['f₂', 'g₂'], ['f₃', 'g₃'], ['u₁', 'v₁'], ['u₂', 'v₂'], ['u₃', 'v₃']],
      queries: [
        ({ A }) => ({ type: 'exact', first: [A('f₁')], second: [A('g₁')] }),
        ({ A }) => ({ type: 'injective', path: [A('f₁')] }),
        ({ A }) => ({ type: 'surjective', path: [A('g₁')] }),
      ],
    }),
  },
  {
    id: 'first-iso',
    title: 'First isomorphism theorem',
    blurb: 'The map A / ker f → im f induced by f (drawn dashed, ∃!) is an isomorphism.',
    make: () => build({
      modules: [['A', 1, 1], ['B', 3, 1]],
      arrows: [['f', 'A', 'B']],
      constructions: [['ker', 'f'], ['im', 'f'], ['coker', 'ι_f']],
      place: { 'ker f': { x: 0, y: 1 }, 'im f': { x: 3, y: 0 }, 'coker ι_f': { x: 2, y: 0 } },
      later: [['φ', 'coker ι_f', 'im f', 'dashed']],
      queries: [({ A }) => ({ type: 'iso', path: [A('φ')] }), ({ A }) => ({ type: 'induced', arrow: A('φ') })],
    }),
  },
  {
    id: 'pullback-epi',
    title: 'Pullback of an epi',
    blurb: 'In a pullback square, the map opposite a surjective map is surjective.',
    make: () => build({
      modules: [['P', 0, 0], ['A', 1, 0], ['B', 0, 1], ['C', 1, 1]],
      arrows: [['p', 'P', 'A'], ['q', 'P', 'B'], ['f', 'A', 'C'], ['g', 'B', 'C', 'epi']],
      squares: [['pullback', 'p', 'q', 'f', 'g']],
      queries: [({ A }) => ({ type: 'surjective', path: [A('p')] }), ({ A }) => ({ type: 'injective', path: [A('p')] })],
    }),
  },
  {
    id: 'pushout-mono',
    title: 'Pushout of a mono',
    blurb: 'For modules, the map opposite an injective map in a pushout square is injective.',
    make: () => build({
      modules: [['A', 0, 0], ['B', 1, 0], ['C', 0, 1], ['Q', 1, 1]],
      arrows: [['f', 'A', 'B', 'mono'], ['g', 'A', 'C'], ['u', 'B', 'Q'], ['v', 'C', 'Q']],
      squares: [['pushout', 'f', 'g', 'u', 'v']],
      queries: [({ A }) => ({ type: 'injective', path: [A('v')] })],
    }),
  },
];

export function exampleById(id) { return EXAMPLES.find(e => e.id === id); }
export { arrowById };
