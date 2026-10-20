# Lean brief: the (7,5) record 1152 from S_4 × Z_24

Goal: `theorem nb_7_5_v2 : ∃ G : SimpleGraph (Fin 1152), BipartiteDD.IsBipartiteDegDiam G 7 5`, through the Haar
lemma on master (`BipartiteDD.Haar.haar_isBipartiteDegDiam_of_equiv`), the same way as `Haar/Record2620.lean` and
`Haar/Record2640.lean` (read those and their Cert files and research/d5/make_haar_cert_2640.py first).

## Autopilot rules (always)
- Before each step, run `scripts/stop_check.sh`. If it prints STOP: commit what you have, push, and end.
- Long commands through `scripts/guarded.sh HOURS ...`. Total time limit: 4 hours. One heavy module at a time.

## The graph
Group G = S_4 × Z_24 (order 576): in Mathlib `Equiv.Perm (Fin 4) × Multiplicative (ZMod 24)`, product
(f, c)·(h, d) = (f ∘ h, c + d). Connection set S (7 elements), each a permutation in one-line form [f 0, f 1, f 2, f 3]
and an element of Z_24:
([0,1,2,3], 0), ([1,0,3,2], 23), ([3,1,0,2], 0), ([2,1,0,3], 18), ([1,2,3,0], 18), ([0,2,3,1], 17), ([0,2,1,3], 3).
Edges (x,A)~(s·x,B). (This is PGL(2,3) × Z_24 acting on the projective line {0,1,2,∞=3}; the main session checked
this exact permutation graph with scripts/verify_record.py: VALID, 7-regular, diameter 5, 1152 vertices.)
Certificates: for every g ∈ G, words showing g ∈ (S⁻¹S)² and g ∈ (SS⁻¹)².

## Steps
1. Branch `lean-1152` from origin/master. `lake exe cache get`.
2. Certificate script research/d5/make_haar_cert_1152.py, Lean files Haar/Cert1152.lean and Haar/Record1152.lean,
   `#print axioms nb_7_5_v2` in Axioms.lean, regenerate Axioms.out.txt.
3. No `sorry`, `admit`, `axiom` or `native_decide`; only propext, Classical.choice, Quot.sound.
4. Commit and push to `lean-1152`. Short report: files, build result, the axioms line.
