# Lean brief: the (9,5) record 2640 from SL(2,11)

Goal: `theorem nb_9_5_v5 : ∃ G : SimpleGraph (Fin 2640), BipartiteDD.IsBipartiteDegDiam G 9 5`, proved through the
Haar lemma that is already on master (`BipartiteDD.Haar.haar_isBipartiteDegDiam_of_equiv`), the same way
`lean/BipartiteDD/Haar/Record2620.lean` proves 2620 (read it and `Haar/Cert2620.lean`, `research/d5/make_haar_cert.py`).

## Autopilot rules (always)
- Before each step, run `scripts/stop_check.sh`. If it prints STOP: commit what you have, push, and end.
- Run every long command through `scripts/guarded.sh HOURS ...`. Total time limit: 4 hours.
- Build one heavy module at a time (`lake build <module>`); parallel kernel checks ran out of memory last time.

## The graph
Group: SL(2,11), 2×2 matrices over ZMod 11 with determinant 1 (Mathlib: `Matrix.SpecialLinearGroup (Fin 2) (ZMod 11)`,
or any group of order 1320 you can prove isomorphic, e.g. a multiplication table on Fin 1320 with a certified encoding).
Connection set S, matrices [[a,b],[c,d]] written (a,b,c,d):
(1,0,0,1), (0,1,10,9), (1,1,9,10), (10,7,4,4), (9,10,4,7), (0,4,8,4), (3,4,0,4), (7,9,2,9), (9,4,4,8).
Edges (g,A)~(s·g,B). The graph file is research/d5/graphs/haar_d9_n2640_sl2_11.json (passes verify_record.py).
The Haar lemma needs (S⁻¹S)² = G and (SS⁻¹)² = G; generate certificates (a witness word for every element) with a
script like make_haar_cert.py.

## Steps
1. Branch `lean-2640` from origin/master. `lake exe cache get`.
2. Write the certificate generator and the Lean files (Haar/Cert2640.lean, Haar/Record2640.lean), add them to
   Axioms.lean, build, regenerate Axioms.out.txt.
3. No `sorry`, `admit`, `axiom` or `native_decide`; `#print axioms nb_9_5_v5` must list only propext, Classical.choice,
   Quot.sound.
4. Commit and push to `lean-2640`. Short report: files, build result, the axioms line.
