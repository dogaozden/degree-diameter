# w16 NOTES (handsoff-49 round 2): grow the 4,970 graph through its quotients

Start: 2026-10-31 23:54 UTC. End: about 02:00 UTC. Card: cards.md, "## w16".

## Quotients built (quot.py, verified)
- G = Z_71 x|_49 Z_35 (index a + 71 j), S = {(0,0),(6,18),(30,19),(30,22)}. N_k = {(a, k t)} normal of index k, k | 35.
  G/N_k = Z_k, so the quotient base is H(Z_k, {s_j mod k}): k+k vertices, 4k simple edges (all k in {5,7,35} work).
- Voltage group N_k = meta:71:(35/k):(49^k mod 71): k=5 -> meta:71:7:45 (order 497, base 5+5);
  k=7 -> meta:71:5:54 (order 355, base 7+7); k=35 -> meta:71:1:1 (order 71, base 35+35).
- Files: bases/q5.base, bases/q5.volt (and q7, q35); lift_check.py rebuilds the lift. All three rebuild VALID
  n = 4,970 with apsp (out/lift_q5.edges, out/lift_q7.edges, out/lift_q35.edges); flift eval gives cost 0 for q5, q7.

## Calibration (the optimizer is the bottleneck)
- flift SA, 5+5 over meta:71:7:45, 60 s: cost 92 (from random). tabu (TABU=1), 60 s: cost 68.
- wl2 (w8's annealer, cost = far (root, vertex) pairs), 5+5 over meta:71:7:45, 60 s: cost 98. So the known cost-0
  lift is NOT rediscovered from random voltages (497^11 space, 11 free voltages after gauge).
- 7+7 over meta:71:5:54, tabu 30 s: cost 126.
- 35+35 over Z_71 (140 edges, 71 free voltages): wl2 120 s: cost 810. flift is about 50x slower there (its cost
  loops over each root separately: b^2 work per evaluation), so use wl2 for bases with b > 20.
- Reading: a 4-regular lift at n about 5,000 gets about 7 far vertices per base root from random voltages;
  the known solution is cost 0, but it is not reachable by plain annealing. This matches w5 (h=5..8 bases stuck).

## Scan (wl2, 6 s per group, 1 seed): 5+5 base over metacyclic groups of order 498..530
- scan5.tsv (rows: order, spec, cost). Ranking below in the final section.
