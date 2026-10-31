# c6 notes (Haar graph + twisted matching)
Family: vertices a_x (x<m), b_y (m+y), m=|G|. Edges a_x~b_{x s_i} (i=1..5) and a_x~b_{sigma(x)} for an arbitrary
permutation sigma of G (sigma = phi(x) t, so every twisted matching is in the family). sigma = x t gives the Haar graph.
Tool: tw.c (SA over sigma swaps and S changes, full bit-parallel BFS cost = unordered pairs at distance > 5).

## 15:45-16:20 log
- tw.c: SA over (S = 5 translations [+ 6th element T as twist in MODE=haar], sigma = arbitrary permutation swaps in gen mode).
  Options: key=value (MODE=haar|gen, INIT=haar|random, S=a,b,c,d,e,f, T0, T1, IPC, RESTART=random, PSDEN). Cost = unordered bad pairs.
- Scorer checked: tw cost == score65 on its output; mcos S={113,16,280,65,59,295} on sg_342_12 (=C6xC19:C3) gives bad 0 (684 Haar).
- Random 6-regular bipartite on 684 vertices: bad ~ 11-12k (score65). General-sigma SA from random: ~3500 after 60 s.
- Haar-mode SA (6 translations) on sg_342_12: plateaus at 684 bad (random restarts, 150-800k evals); mcos "1|1" finds 0 in 41 s,
  so the plain SA is weaker than mcos on the Haar landscape (mcos uses conjugacy-class-restricted S and per-rep cost).
- Timing: eval ~0.1 ms at n=686. Foreground Bash must pass timeout=600000 for runs longer than ~100 s.
- Groups: tabs made with GAP (7 s for order 343). sg_342_12 = C6 x (C19 : C3); sg_343_{1..5}.
