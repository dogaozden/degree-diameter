# Lean brief: three diameter-5 Haar records (1152, 1764, 2662) — Sonnet

All three go through the Haar lemma on master (`BipartiteDD.Haar.haar_isBipartiteDegDiam_of_equiv`), exactly like
`Haar/Record2620.lean` and `Haar/Record2640.lean` (read them, their Cert files, and research/d5/make_haar_cert_2640.py).
A Haiku session started 1152 on branch `origin/claude/lean-1152-4u9f42` (certificate script only, then stalled past its
time limit); reuse it if useful. Work on branch `lean-haar3` from origin/master.

## Autopilot rules (always)
- Before each step run `scripts/stop_check.sh`; if it prints STOP, commit, push, end.
- Long commands through `scripts/guarded.sh HOURS ...`; total limit 5 hours; one heavy module at a time (parallel kernel
  checks ran out of memory before). Push after each record.

## The records (all checked with scripts/verify_record.py; graphs in research/d5/graphs/, each JSON's "construction"
## field has the group and S)
1. `nb_7_5_v2 : ∃ G : SimpleGraph (Fin 1152), IsBipartiteDegDiam G 7 5` — G = S_4 × Z_24 as
   `Equiv.Perm (Fin 4) × Multiplicative (ZMod 24)`; S (one-line perm [f 0,f 1,f 2,f 3], c): ([0,1,2,3],0),
   ([1,0,3,2],23), ([3,1,0,2],0), ([2,1,0,3],18), ([1,2,3,0],18), ([0,2,3,1],17), ([0,2,1,3],3). See docs/lean-1152-brief.md.
2. `nb_8_5_v2 : ∃ G : SimpleGraph (Fin 1764), IsBipartiteDegDiam G 8 5` — G = AGL(1,7) × Z_21. Element
   ((b,a),c): the map t ↦ a·t+b on ZMod 7 (a ≠ 0) paired with c ∈ ZMod 21; (b1,a1)(b2,a2) = (a1·b2+b1, a1·a2).
   S: ((0,1),0), ((0,4),5), ((6,6),18), ((6,5),6), ((2,4),1), ((2,2),16), ((4,5),12), ((2,6),15).
   (research/d5/graphs/haar_d8_n1764.json)
3. `nb_9_5_v6 : ∃ G : SimpleGraph (Fin 2662), IsBipartiteDegDiam G 9 5` — G = Heisenberg group mod 11, (a,b,c) =
   [[1,a,c],[0,1,b],[0,0,1]], (a,b,c)(a',b',c') = (a+a', b+b', c+c'+a·b') mod 11. S: (0,0,0), (8,6,10), (7,9,3),
   (10,1,8), (4,4,5), (5,5,8), (6,5,4), (1,0,9), (6,10,8). (research/d5/graphs/haar_d9_n2662.json)
Edges (x,A)~(s·x,B) in each case. You may model each group concretely (a structure with a `Group` instance, or a
product of Mathlib groups); prove its cardinality.

## Finish
`#print axioms` for the three in lean/Axioms.lean; regenerate lean/Axioms.out.txt. No `sorry`, `admit`, `axiom`,
`native_decide`; only propext, Classical.choice, Quot.sound. Push `lean-haar3`. Report: files, build, axioms lines.
