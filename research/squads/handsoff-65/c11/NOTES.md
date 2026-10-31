# c11 notes (round 2, card: 2+2 lifts with an imposed swap symmetry)

## Result so far (18:25 UTC)
- No graph with n > 684 and bad = 0. Best n > 684 candidate: n = 704, swap-symmetric lift, cost 58 = bad 5104 (s704.edges).
  Unsymmetric c1 floor (cost 4, bad 352) is far better: the symmetric subspaces found here are much worse for nonabelian groups.
- Positive: the abelian swap family with f = identity gives diameter-5 lifts quickly up to cyclic m = 140 (n = 560).
  Verified: cyc140 solution (sw140.sol -> sw140.edges) passes shared/check.sh: bad = 0, diam = 5, n = 560, RESULT VALID.

## Setup
- Base: 2+2 vertices 0=A1, 1=A2 (side 0), 2=B1, 3=B2 (side 1). Classes A=(0,2)xa, B=(0,3)x(6-a), C=(1,2)x(6-a), D=(1,3)xa.
- Swap sigma: A1<->B2, A2<->B1 (vertices 0<->3, 1<->2): maps A<->D and maps B and C to themselves.
- Lift symmetry: for an involutory automorphism theta of G, tau(v,h) = (sigma v, theta(h)) is an automorphism of the lift
  iff volt(sigma e) = f(volt e) with f(g) = theta(g)^-1 (f is an involution). Self-fixed edges (B, C) need f(volt) = volt.
  Side-preserving sigma' = (A1 A2)(B1 B2) (theta = id, f = id) was also tried (mksym2.py); poor.
- Tools (c11/, all my own): tsym.c (tabu over the symmetric space, same cost as shared/tabu.c; SYM file gives the tie
  structure, FMAP=file gives f); mksym.py a pB pC (swap family; pB/pC = number of 2-cycles of sigma in classes B, C);
  mksym2.py (side-preserving); verify_sym.py (numerical check of an automorphism, theta = id only);
  invs.g / invs2.g (GAP: involutory automorphisms of SmallGroup(m,i), f maps; invs2 = one per Aut-conjugacy class).
- Group tables: tabs/sg_<m>_<i>.txt (GAP), tabs/cyc<m>.txt, tabs/id<m>.txt (identity map for f = id).
- Calibration: cost 0 for cyclic m = 100, 120, 140 with f = id (0.1, 0.5, 4 s). Unsymmetric tabu does the same cyclic cases.

## Experiments and numbers
1. Swap with theta = id (f = inverse), groups of order 176 (sym_screen.tsv, 5 s each; 21 groups, options a2 p1q1, a2 p2q2):
   best 52 (176/3 C8xD22), 60 (176/4), 64 (176/16), 84 (176/17 C11:Q16). 60 s runs: 176/17: 88, 64; 176/3: 52.
   Cyclic 140 with theta = id: 124-152 (no cost 0 at all). => theta = id is a poor symmetry.
2. Abelian groups, f = identity (theta = inversion), a = 2 (cost after 10 s; ab_screen.tsv): C172 60, C86xC2 64,
   C174 62, C176 72, C44xC4 52. (a=1 and a=3 similar.) Cyclic sweep (8-20 s): m=144: 8; 150: 4; 156: 24; 160: 28;
   164: 36; 168: 60; 172: 44 (20 s). So the cyclic frontier of this family is m about 145-150 (n about 580-600).
3. Involutory automorphisms of 171/4 = C3 x (C19:C3) (the group of the 684 graph): 80 maps (4 Aut-classes, fixed-point
   counts 1, 3, 19, 57), all screened (maps_screen.tsv, 5 s, a2 all pairs): best 12 (f with 3 fixed points), 16, 36 (fix 57).
   The 684 graph was NOT reproduced in this family (calibration failed), so the 684 graph is not swap-symmetric in this form
   or tabu cannot find it.
4. Order 176, one run per Aut-class of involutory theta (cls_screen.tsv, 5 s, a2 all pairs; batch run176.sh, groups in order):
   best cost per group: 176/1 C11:C16: 58; 176/2 C176: 64; 176/3 C8xD22: 89; 176/4: 84; 176/5 C11:QD16: 116; see cls_screen.tsv.
   Cost 58 = bad 5104 at n = 704 (cost in units of m/2 far pairs; c1's cost 4 = bad 352).

## Reading
- theta = id and all nonabelian involutory theta tried: floors 50-120 at 5-60 s, far above the unsymmetric floor 4.
- The only symmetric family that hits cost 0 quickly is abelian with f = id; its cyclic frontier (about n = 600) is below 684.
- Swap symmetry does not look like the route to 686+ with 2+2 bases. The unsymmetric tabu floor at 176 (cost 4) stays best.

## Next ideas (not done)
- Long (5 min) runs of the best nonabelian swap candidates (176/1 k6, 176/2) with polishing by shared/tabu from them.
- Other symmetric types: sigma of order 2 that fixes a vertex pair and swaps the others (needs a = 3); 3+3 bases with swap.

## Final results (19:20 UTC)
- Order-176 batch complete (cls_screen.tsv, 693 rows, 5 s per run, one run per Aut-class of involutory theta, option a2 all pairs,
  5 groups failed to start). Best cost per group (min over classes): 176/19 (C44xC4, abelian) 24; 176/25 40; 176/20 42;
  176/26 42; 176/23 44; 176/39 (C22 family) 54; 176/1 58; 176/12, 176/7, 176/9, 176/40 48; 176/2 (C176) 64; 176/3 89; 176/4 84.
  Cost 24 = bad 2112 at n = 704 (c11/s704.edges, scoreboard line 19:15).
- Caution: the 5 s numbers are noisy. Re-runs of the best map of 176/19 (60 s, seeds 101, 102): 68 and 72; 20 s: 48.
  So 24 is a lucky draw; the true floor for these families is around 40-70 at 704 vertices, far above the unsymmetric floor 4.
- Full list of costs: cls_screen.tsv (columns: order, id, name(first word), class k, fixed points of f, cost).
- No process of c11 left running at the end.

## Conclusion
- The swap symmetry with theta in Aut(G) does not reach cost 0 (or anything near the unsymmetric floor) at n about 700,
  except that the abelian family with f = identity (theta = inversion) gives diameter-5 lifts up to n = 560 (cyclic 140).
- No graph above 684 vertices with diameter 5 was found by c11.
- 85 s polishes (19:21): 176/19 k7 -> 56; 176/25 k3 -> 52; 176/20 k2 -> 40. Nothing below the 5 s best of 24. Stopped at 19:22.
- Personal-best scoreboard lines (c11): 18:19 bad 5104 (cost 58), 18:49 bad 4224 (cost 48), 19:15 bad 2112 (cost 24); file c11/s704.edges.
- Other bases on 176/19 (5 s, maps k7, k3, k2, k8): a=3 (pB=pC=1): 52, 40, 40, 72; a=1 (pB=pC=2): 148, 132, 144, 331. a=2 is the best base.
- Ending state (19:23 UTC): no c11 processes running; scoreboard has 3 c11 lines (best bad 2112, n=704, c11/s704.edges).
