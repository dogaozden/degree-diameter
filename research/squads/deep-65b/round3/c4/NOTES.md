# c4 (round 3): cyclic Z_N lifts of the 8-vertex split base

Folder: research/squads/deep-65b/round3/c4/. Time box 45 min (started 00:45 UTC, stopped about 01:06 UTC).

## Files
- lift8.c, binary lift8 (`gcc -O3 -march=native -o lift8 lift8.c`). Usage: `lift8 DARTS N SEED SECS [OUT.edges]`.
  lift8_v1.c is the earlier byte-array version of the same cost (identical outputs, about 4x slower).
- make_darts.py: `python3 make_darts.py record` writes record_darts.txt (the 24 darts of records/build_d6D5_n704_z88.py,
  base matrix [[1,0,3,2],[0,1,2,3],[2,3,1,0],[3,2,0,1]] checked); `python3 make_darts.py pq P Q` writes base_P_Q.txt
  (rows [1,0,P,5-P],[0,1,5-P,P],[Q,5-Q,1,0],[5-Q,Q,0,1], all voltages random).
- pert_k{1..4}_s{1,2}.txt: record darts with k random darts set to random (repair test).
- rec_check.edges (record, 704 vertices), rec2.edges (same, after the bitset rewrite), st_*.edges, chk89/90.edges (samples).
- Outputs: calib88_a.txt, calib88_b.txt, sweep_p3q2_a.txt, sweep_p3q2_b.txt, sweep_p3q2_seed3.txt, sweep_p3q2_seed3b.txt,
  sweep_bases_a.txt, sweep_bases_b.txt, sweep_34_a.txt, sweep_34_b.txt, repair88.txt.

## Model
Base: 8 vertices, A index a = 0..3 (A0^0, A0^1, A1^0, A1^1), B index b = 0..3 (B0^0, B0^1, B1^0, B1^1); 24 darts (a, b, w).
Lift by Z_N: fibre (v, x), v = 0..7 (B vertex = 4 + b), dart (a, b, w) gives edges (a, x)-(4+b, x+w). 8N vertices, bipartite,
6-regular. Darts in one bundle keep distinct voltages, so the lift is simple.
Cost = number of pairs (u, (v,x)) with u a base vertex at fibre 0 and (v,x) at distance > 5 from (u,0). Computed by a
bitset BFS (8 sources at once, 5 levels, fibre sets as 128-bit words, rotations for the voltage shifts). Cost 0 iff diameter <= 5.
Relation to score65 (checked on random states): bad = cost x N/2 exactly (N = 88: x44; N = 89: x44.5; N = 90: x45).
Gauge: a spanning tree of the base (7 darts) is fixed at voltage 0 (the start is shifted to that gauge), leaving 17 free darts.
Search: tabu over single free-dart changes (no duplicate in a bundle), full neighbourhood (about 1480 moves per step),
tabu on (dart, old value) with tenure 6-15, aspiration, restart (3 random moves) after 400 steps without a new best.
Speed: about 55-60 steps/s at N = 88..100.

## Calibration (card c4 (1))
- Record voltages (record_darts.txt, N = 88): cost 0. `score65 rec_check.edges`: bad = 0, `apsp rec_check.edges 6 5`:
  RESULT VALID d=6 D=5 n=704. The evaluator and the lift model reproduce the record.
- Consistency with score65 on 6 random states (N = 88): cost 360, 428, 308, 302, 273, 282 vs bad 15840, 18832, 13552,
  13288, 12012, 12408 (ratio 44 each).
- Tabu repair from the record (repair88.txt, 10 s): k = 1 random dart: repaired at once (one move back); k = 2: repaired in
  1 of 2 seeds; k = 3 and 4: not repaired (best 37-39). The zero set is a tiny basin for this tabu.
- Random starts, N = 88 (base (3,2)), 0 of 4 runs reach 0: 30 s seeds 1, 2, 3 -> best 35, 36, 40; 20 s seed 4 -> best 34.
  Also 10 s seed 7 -> best 36. So the tabu does NOT find the known n = 88 solution from random starts.

## Sweep n = 89..100 (lift sizes 712..800), best cost over runs
Base (3,2) = the record base; seeds 1 (15 s), 3 (10 s) for n = 89..100:
  n:    89  90  91  92  93  94  95  96  97  98  99  100
  s1:   48  34  50  50  52  66  68  80  78  89  96   98
  s3:   38  46  50  54  52  62  66  70  80  86  94   96
Bases (3,3) and (4,4), seed 2 (8 s for n <= 93, 7 s for n >= 94):
  (3,3): 40 46 38 56 62 66 70 81 86 96 102 100
  (4,4): 40 52 56 62 62 86 72 96 88 100 120 116
All 16 bases (p, q in 1..4) at n = 89, seed 1, 10 s: 1_1 48, 1_2 44, 1_3 54, 1_4 78, 2_1 46, 2_2 46, 2_3 44, 2_4 54,
  3_1 58, 3_2 48, 3_3 40, 3_4 44, 4_1 82, 4_2 58, 4_3 44, 4_4 40.
Best per n over all runs: 89: 38, 90: 34, 91: 38, 92: 50, 93: 52, 94: 62, 95: 66, 96: 70, 97: 78, 98: 86, 99: 94, 100: 96
(cost; bad pairs = cost x N/2, so cost 34 at N = 90 is 1530 bad pairs).
No zero for N = 89..100 on any base or seed. The best cost grows with N, roughly +6 per unit of N.

## Reading
- Negative for this card: no abelian Z_N lift of the (4+4)-split bases with N = 89..100 was found, and the search cannot
  even recover the N = 88 record from random starts (0 of 4). So these numbers say the tabu is too weak for this family,
  not that the family is empty. An exact method is needed before any claim about N = 89..100.
- Suggested next step: an exact search over the 17 free voltages in Z_N (the six-condition sumset form of split15 applies
  to abelian groups too: the 8 sources give word conditions), or a branch and bound on the walk words, for N = 89, 90, 92,
  96 first. Brute force over Z_N^17 is out of reach.
