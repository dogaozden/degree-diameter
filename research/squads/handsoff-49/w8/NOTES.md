# w8 NOTES (wildcard)

Start: 2026-10-31 21:41 UTC. Stop (2 hours): about 23:41 UTC.

## Best so far (no valid record)
- n = 4992 (base 2+2, multigraph [[1,3],[3,1]] = base4p1.txt; group agl1 13 x cyc 8, groups2/h03.bin, order 1248),
  cost 15 = far pairs 15*1248/2 = 9,360 (score48 counts far pairs; cost = 2*far/K). Final at 23:12 UTC.
  File: w8/runs/w8_best_n4992.edges (voltages w8/runs/w8_best_n4992.sol, format "K m" then one voltage per base edge).
  Rebuild: from scratch `./wt base4p1.txt groups2/h03.bin 9 450 8 runs/T3 1000 20` (SA start then tabu chain
  T2 -> T7 -> T8, each `wt ... 450 SEED OUT 2000 40 <previous .sol>`); latest solution is runs/w8_best_n4992.sol.
  Not valid: `apsp` prints INVALID at D = 9.
- Calibration: the same tools reproduce the valid 4,970 Haar graph's voltage set (score48 VALID) when given it; random
  search does not find it on the dipole base (cost 2 after 60 s).

## Tools (all in w8/)
- wl.c / wl: groups <= 64. wl2.c / wl2: simulated annealing, groups <= 4096, bases <= 256 vertices, parallel base edges
  (duplicate voltages penalised). Usage: `wl2 BASE GROUP.bin D seconds seed OUT [T0 T1]`, BASE = "b" then "u v" lines.
- wt.c / wt: tabu search over cotree voltages, same model. Usage: `wt BASE GROUP.bin D seconds seed OUT NS TT [INIT.sol]`.
- Evaluator: bitset walk propagation over all roots at once; checked against score48 (far = cost*K/2).

## Findings
- Lifts of the (4,5) record graph (162 vertices, bipartite, vertex-transitive) over groups of order 31..40:
  cyclic groups stall at cost ~2,150; non-abelian groups at 3,100-3,500 (35 s screen). Dropped: the number of
  (pair, element) constraints scales with b^2 k, so a 162-vertex base is far too constrained for SA.
- Small bases with groups of order 1248..1320 (n = b k >= 4,972): screened in 40 s each (screen2.txt, screen3.txt).
  base 2+2 [[1,3],[3,1]] (base4p1): best groups AGL(1,13) x Z8 (cost 24), Z5^2 x| Z50 (40), dih 625 (9408), others
  48-200. base 2+2 doubled C4 (base4p2): AGL(1,13) x Z8 cost 30, Z5^2 x| Z50 cost 34.
- Long SA (470 s) on the best pair stalls at cost 26; tabu search (NS = 1000 sampled moves, tenure 20) takes it to 18,
  then (NS = 2000, tenure 40) to 16 and 15; the last two rounds stall at 15.
- Doubled-C4 base (base4p2) from random tabu: cost 24 (450 s). 3+3 bases (base6_M1, SL(2,5) x Z7, n = 5040): SA 34,
  tabu 32 (450 s). So 2+2 with [[1,3],[3,1]] is the best of the small bases I tried.
- Structural note: the uncovered (root, lift vertex) pairs are almost all same-side pairs (even walks of length <= 8).
  Walks per element are about 3.5 for n about 5000, which is the same for every base; so larger bases have more
  constraints and fewer per variable. The b = 2 Haar family (w1/w2) is the natural home for records.

## Not done / next ideas
- 3+3 bases screened only on SL(2,5) x Z7 (screen6.txt); other groups untested.
- Tabu with larger NS, restarts from several SA solutions, or a symmetry restriction (voltages invariant under a
  base automorphism of order 2) to shrink the search.

## Final (23:20 UTC)
- Last tabu round (4000 moves, tenure 40, 440 s) did not improve on cost 15. Best stays n = 4992, cost 15,
  far pairs 9,360, file w8/runs/w8_best_n4992.edges (checked: score48 far = 9360, apsp INVALID at D = 9).
- Next idea: the same tabu search on the b = 2 Haar family (w1/w2 territory) at orders 2,486..2,520, where tabu
  should beat the plain annealing used by the dipole calibration; and restarts from several SA solutions.
