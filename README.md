# Persistence Module Diagram Chaser

**Live: https://primozskraba.github.io/diagram-chaser/**

A graphical editor for commutative diagrams of finitely generated k[t]-modules
(persistence modules). Draw modules and maps, mark maps injective, surjective,
isomorphisms (≅), identities (=), zero or induced (∃!), add kernels, images,
cokernels, exactness, pullbacks and pushouts, and ask diagram-chase questions:
is a map injective, surjective, an isomorphism or zero, is a sequence exact,
does an induced map exist? Every positive answer comes with a proof in words and
a Lean 4 / Mathlib theorem; every negative one with a finite-dimensional
counterexample. Click **Help** in the app for the editing controls.

Everything runs in your browser. Nothing is uploaded; diagrams are kept in your
browser's storage and can be saved and opened as JSON files.

## Checking the Lean proofs

On the website, use **Open in Lean 4 Web** (live.lean-lang.org). It loads the
latest Mathlib, so the first check can take a minute or two. If it does not open
the proof or reports errors — very long proofs, a busy server, or a change in a
newer Mathlib — use **Download .lean** (or **Copy Lean**) and check the file with
your own Lean, or run the app locally with proof checking built in.

## Run it locally

You need Python 3; Lean is optional.

```bash
git clone https://github.com/primozskraba/diagram-chaser
cd diagram-chaser
python3 server.py            # then open http://127.0.0.1:8765
```

For proof checking, install Lean with [elan](https://lean-lang.org/install/)
and make a Mathlib project once, inside `diagram-chaser`:

```bash
lake +leanprover-community/mathlib4:lean-toolchain new lean-project math
cd lean-project && lake exe cache get && cd ..
python3 server.py            # finds ./lean-project: "Check with local Lean" is enabled
```

An existing Mathlib project works too: `python3 server.py --lean-project PATH`
(or set `LEAN_PROJECT`). To check a downloaded proof by hand:

```bash
cd lean-project && lake env lean ~/Downloads/DiagramChase.lean
```

No errors means Lean accepted the proof. Some browsers save the download as
`DiagramChase.lean.txt`; rename it, or pass that name to `lake env lean`.
