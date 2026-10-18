Lean 4 + Mathlib work, two tasks in order. Work on your own for up to 4 hours; do not ask for approval. Lean checks every proof; iterate until builds pass. Push after every milestone.

Setup: `git fetch origin && git checkout -b lean-final origin/claude/lean-records3-graphs-6719pq && git merge origin/research-diam4` (take research-diam4's version for conflicts outside lean/). Install elan (`curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none`, `source ~/.elan/env`), `lake exe cache get` in lean/. `git push -u origin HEAD`.

## Task 1 (quick): the (16,3) record graph
Add `nb_16_3 : ∃ G : SimpleGraph (Fin 396), BipartiteDD.IsBipartiteDegDiam G 16 3` for records/bipartite_dd/d16D3/396-d3d6-sym3_q13_d16_n396.json, using the existing pipeline (gen.py; plain `checkFast` should suffice at 396 vertices, otherwise the staged method). Add it to Axioms.lean, regenerate Axioms.out.txt, commit `milestone: nb_16_3`, push.

## Task 2: Proposition C (Singer-orbit 2-ovoids of W(3,q))
Read research/NOTE.md (Proposition C and its proof) and research/gq4y/w3_singer.py. Statement: F finite field of odd order q, K a degree-4 extension (or work in GaloisField p (4e)), g a generator of Kˣ, d = g^((q²+1)/2), B(x,y) = Tr_{K/F}(d·x·y^{q²}). Points of PG(3,q) = Kˣ/Fˣ. For every 2-dimensional F-subspace U of K that is totally isotropic for B, the number of points of U (1-dim F-subspaces) lying in classes a or q−a (class of g^i is i mod q+1) is exactly 2.
Prove as much as you can, in this order, pushing each proved lemma:
(a) B is a nondegenerate alternating F-bilinear form, and multiplication by g^(q+1) scales it (so classes are preserved by the isometry group generated).
(b) The norm/class characterization: g^i is in class a iff N_{K/L}(x) ∈ h^a Fˣ where L = GF(q²), h = g^(q²+1).
(c) The discriminant identity D(hν^q) = N(h)·D(ν) and the counting 1 + χ(D) on each line, giving the theorem.
If the full statement is out of reach, prove it for a fixed small field by `decide` only if it is genuinely kernel-checkable (no native_decide), else stop and report exactly which lemmas are done.

## Rules
No `sorry`, `admit`, new `axiom`, `native_decide`, or checking-weakening options. Do not edit GQ4/, GQST/, ASq/, Plus2/, Staged.lean, Fast.lean, Basic.lean or existing graph data. New code under lean/BipartiteDD/SingerC/ for Task 2. At the end add new theorems to Axioms.lean, regenerate Axioms.out.txt, commit `milestone: ...`, push.

## Final reply
What builds, statements proved (copy them), `#print axioms` lines, what is open, last commit hash.
