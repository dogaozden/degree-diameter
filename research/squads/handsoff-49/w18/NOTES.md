# w18 NOTES: auditor for handsoff-49 (follows w13)

Start: 01:03 UTC. Runs until 02:50 UTC. Re-audit of new scoreboard lines every 20 minutes.
Files: audit.tsv (one row per scoreboard data line, 49 rows at 01:35), build_audit.py (regenerates it), raw/ (score48 and
apsp output per edge file), indep_run*.txt (pure-Python BFS, independent of the tools), repro_w11.tsv (w11 re-runs),
val/ (brute force calibration, rebuilt graphs), girth_h3.py.

## Status (01:35 UTC)
- Records: none. No line is VALID at d=4, D=9 with n > 4,970. Nothing copied to records/.
- VALID lines: line 7 (w3, n = 3200) and line 48 (w16, n = 4970, rebuild of the known table graph). Neither is a record.
- Scoreboard changes since the squad started: lines 48, 49 (w16, 01:15). No other new lines.

## Per-worker best verified near miss (n > 4,970; far = pairs at distance > 9)
Every edge file below was checked with score48 and apsp (d=4 D=9): degree 4, bipartite, connected, diameter as listed.
Re-checked with w18/indep_far.py (pure Python BFS from every vertex): lines 1, 2, 9, 12, 17, 19, 21, 22, 24, 35, 36, 39, 40, 43, 47, 49 and the rebuilt 38 and 46.

| worker | best verified n > 4970 | cost | far pairs | diam | edge file (scoreboard line) |
|---|---|---|---|---|---|
| w1 | 5040 | 6 | 7560 | 10 | w1/t/A7_cost6.edges (10) |
| w2 | 5050 | 2 | 2525 | 10 | w11/out/m101_k25_r5_c2.edges (same group, w2 wrote no edge file; 14) |
| w3 | 5040 | 906 | 28539 | 10 | w3/runs/rep63_best.edges (6) |
| w4 | 4992 | 76 | 15808 | 10 | w4/r12m13_76.edges (35) |
| w5 | 4992 | 4 | 2496 | 10 | w5/out/f_39_32_31_s72.edges (32) |
| w6 | 4972 | 160 far | 160 | 10 | w6/tmp/surgsa4_best160.edges (2) (best far count overall) |
| w7 | 5200 | 30 | 39000 | 10 | w7/best_psl25_h3_C30_n5200.edges (1) |
| w8 | 4992 | 15 | 9360 | 10 | w8/runs/w8_best_n4992.edges (17) |
| w9 | 5040 | 15 | 18900 | 10 | w9/runs/S7_h2_K2.edges (24) |
| w10 | 5040 | 8 | 10080 | 10 | w10/runs/S5xF21_cost8.edges (40) |
| w11 | 5050 | 2 | 2525 | 10 | w11/out/m101_k25_r5_c2.edges (21) (exact minimum for this group) |
| w12 | 5280 | 64 | 42240 | 10 | w12/runs/d2_r21.best.edges (43) |
| w13 | 4992 | 4 | 4992 | 10 | w13/best_haar_104_24_7_c4.edges (39) |
| w14 | 5040 | 312 | 393120 | 11 | w14/runs/K_PSL34_h8_H3_K5_c0.edges (47) |
| w15 | 5000 | 4 | 5000 | 10 | w18/val/u4m7_c.edges (rebuild of 46; scoreboard says n = 2500) |
| w16 | 5040 | 82 | 20664 | 10 | w16/out/wl_q5_meta_14_36_3.best.edges (49) |

Overall: fewest far pairs above 4,970 is w6 (n = 4972, 160 far pairs). Lowest cost above 4,970 is 2 (n = 5050, w11 group
101 25 5, exact minimum 2 for that group, so it cannot reach 0). Cost 4 at n = 4992 (w5, w11, w13) and n = 5000 (w15).

## Discrepancies (for the coordinator; I did not edit scoreboard.tsv)
1. Stale path: lines 3, 8, 15, 17 all name w8/runs/w8_best_n4992.edges, which w8 overwrote. The file now has far = 9360
   (cost 15, line 17). The claims 24, 18 and 16 (lines 3, 8, 15) cannot be reproduced from the path any more.
2. Wrong n: lines 38 and 46 (w15) say n = 2500. The Haar graph of a group of order 2500 has 2|G| = 5000 vertices (w15's own
   NOTES says n = 5,000). Rebuilt by w18: u4m7_c.edges (cost 4, far 5000) and hb1_c.edges (cost 10, far 12500), both n = 5000,
   diameter 10. So line 46 is a cost-4 near miss above 4,970, not a 2,500 one. Please correct the n column.
3. Missing file: line 4 (w1, A7_near_cost6.edges) never existed. Line 10 is w1's own correction (same cost 6, same group);
   line 10 is checked and holds.
4. Paths that are not edge lists: line 6 (.volt, rebuilt from runs/rep63_best.edges, holds), 13 and 14 (w2 deep.tsv rows,
   same groups as w11 files, hold), 16 (w1 .out, reproduced), 38 and 46 (w15 .bin tables, rebuilt).
5. w11 asked the coordinator to drop 12 of its own early lines (before 23:30). I confirmed each is a tie or worse than an
   earlier line at the same n: lines 21-23, 25-31, 33, 34. Lines 25-34 and 41-45 have no file (exhaustive claims, see below).
6. Column meaning: cost_or_far mixes units. Line 2 is a far-pair count. For Haar and lift lines cost = 2 far / |G|
   (|G| = 2520, 1248, 832, 416, 1320, 622, 2496, 63, ...). For bi-coset lines (w7, w9, w14) far = M C / 2 with M = |G|/|H|.
   Every edge line matches its formula (audit.tsv column expected_far_from_claim) except the stale lines 3, 8, 15.

## Certified (exhaustive) negative results, and what w18 reproduced
- w11 exh3 (certified.tsv, split metacyclic groups, D = 9, minimum cost over all S = {e,x,y,z} up to Aut and translation):
  `cd w11 && ./exh3 meta M K R 100000 TAG 500 9` (or run_any.sh). w18 re-ran 26 split groups with the same binary in its own
  folder; every minimum matched: 101_25_5 = 2, 104_24_7 = 4, 208_12_3 = 4, 35_72_4 = 6, 105_24_17 = 6, 208_12_141 = 6,
  420_6_109 = 6, 70_36_9 = 8, 208_12_29 = 8, 208_12_37 = 8, 208_12_43 = 8, 208_12_11 = 9, 104_24_11 = 10, 35_72_3 = 10,
  105_24_2 = 10, 210_12_23 = 10, 210_12_79 = 10, 115_22_4 = 10, 215_12_92 = 10, 208_12_115 = 10, 52_48_7 = 12, 208_12_69 = 12,
  416_6_367 = 12, 105_24_52 = 12, 320_8_7 = 12, 427_6_13 = 12. Non-split rows of certified.tsv were not re-run.
  Calibration of exh3 against brute force (w18/val/brute.c: every S, no symmetry): 9 cases (metacyclic groups of order
  110 to 156 with D = 3, 5, 7, 9), all minima equal (e.g. 15_8_2 D=5: 38 both; 13_12_2 D=5: 102 both; 15_8_2 D=3: 214 both).
- w1 exh (A_7, Haar graphs, class representatives of the 8 non-identity classes): min cost 6, zeros 0. Re-run of the class
  of element 19 (`cd w1 && ./exh tabs/A7.bin 6 5 6`): evals 3168903, best 6, identical to w1/res/exh_A7_class19.out.
  Other reps in w1/res: best 6 (c01, c23), 7 (c4, c67). Not re-run.
- w7 bicos exh (PSL(2,25), H of order 3, composition {1,3}, 6912 sets): C = 30. Recipe in w7/NOTES.md. Not re-run here; the
  same value 30 comes from w9's independent bi9 code (w9 calibration).
- w9 bi9 exh (bi-coset, exact minima per (G,H) class): M11 H3 = 38, S7 H=K2 = 15, PSL(2,25) H3 = 30, PGL(2,25) order-6 = 30.
  Recipe: `python3 grp9.py M11 3 1500` then `./bi9 <table> exh 0 out.edges` (w9/NOTES.md). Not re-run.
- w14 kbi exh (PSL(3,4), two subgroups of order 8, 9 classes x 81 pairs): minimum 312. Recipe in w14/NOTES.md. Not re-run.
- w4 (proof, no search): a lift of a base of girth g >= 10 has every fibre at pairwise distance >= g, so diameter >= 10 for
  any voltage group. The H(3) incidence graph (seeds/hexagon_q3.json) has girth 12 and diameter 6 (w18/girth_h3.py), so
  the hexagon-lift family cannot give diameter 9 at any n. w4 NOTES says the same.
- Not certified (no exhaustive claim): w2, w3, w5, w8, w10 (partial reps 1-9 only), w12, w13, w15, w16.

## Checks run
- score48 and apsp on the 29 scoreboard edge files (lines 1-3, 5, 7-12, 15, 17-24, 32, 35-37, 39, 40, 43, 47-49) and on the
  rebuilds 6, 38, 46. All agree on diameter and far pairs.
- Pure-Python BFS (w18/indep_far.py): 18 files (the lines listed under per-worker bests, plus the rebuilt 38 and 46),
  all agree with score48 far counts (indep_run1..3.txt).
- Symmetry reduction of w11 exh3 checked against brute force (see above).

## Next
- Re-audit at 01:50, 02:10, 02:30, 02:45 (scoreboard diff; new lines get score48 + apsp + indep_far if they matter).
- If a VALID line with n > 4970 appears: copy to records/, write it first here, and run indep_far.py.
