# w18 NOTES: auditor for handsoff-49 (follows w13)

Start: 01:03 UTC. Runs until 02:50 UTC. Re-audit of new scoreboard lines every 20 minutes.
Re-audit log: 01:15 (lines 48, 49 added by w16), 01:30 (none), 01:47 (none), 01:56 (lines 50 w23, 51 w17 added at 01:48 and 01:50;
both checked, see audit.tsv).
Files: audit.tsv (one row per scoreboard data line, 51 rows at 01:57), build_audit.py (regenerates it), raw/ (score48 and
apsp output per edge file), indep_run*.txt (pure-Python BFS, independent of the tools), repro_w11.tsv (w11 re-runs),
val/ (brute force calibration, rebuilt graphs), girth_h3.py.

## Status (01:57 UTC)
- Records: none. No line is VALID at d=4, D=9 with n > 4,970. Nothing copied to records/.
- VALID lines: line 7 (w3, n = 3200) and line 48 (w16, n = 4970, rebuild of the known table graph). Neither is a record.
- Scoreboard lines added since the audit started: 48, 49 (w16, 01:15), 50 (w23, 01:48), 51 (w17, 01:50). All checked.

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
| w17 | 5040 | 15120 far | 15120 | 10 | w17/runs/A7_r4444_8_deep.edges (51) (far count, not better than w6) |
| w23 | 5000 | 4 | 5000 | 10 | w18/val/w23chk_a.edges, rebuilt from the set {0,620,631,1380} in w23's list (50) |

Overall: fewest far pairs above 4,970 is w6 (n = 4972, 160 far pairs). Lowest cost above 4,970 is 2 (n = 5050, w11 group
101 25 5, exact minimum 2 for that group, so it cannot reach 0). Cost 4 at n = 4992 (w5, w11, w13) and n = 5000 (w15).

## Discrepancies (for the coordinator; I did not edit scoreboard.tsv)
0. Line 50 (w23, "exact floor 4" for u4m_7 at n = 5000): the same group as line 46. w23's exhaustive output covers all
   14 Aut-orbit representatives (runs_rep0, runs_reps1_7, runs_reps8_13: 14 x 3,118,753 sets = 43,662,542), 1,160 sets of
   cost 4, none below 4. The set {0,620,631,1380} rebuilt by w18 has far 5000 (cost 4). Not independently verified: the
   automorphism list (aut_orbits.txt, orbit sizes sum to 2499 = |G|-1, consistent) and the claimed |Aut| = 20000.
   w23 NOTES.md lists orbit sizes with three 100s; the file has four 100s. The file is the one that sums correctly.
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
   earlier line at the same n: lines 21-23, 25-31, 33, 34. Lines 25-31, 33, 34, 41, 42, 44, 45 have no file (exhaustive claims,
   reproduced, see below).
6. Column meaning: cost_or_far mixes units. Line 2 is a far-pair count. For Haar and lift lines cost = 2 far / |G|
   (|G| = 2520, 1248, 832, 416, 1320, 622, 2496, 63, ...). For bi-coset lines (w7, w9, w14) far = M C / 2 with M = |G|/|H|.
   Every edge line matches its formula (audit.tsv column expected_far_from_claim) except the stale lines 3, 8, 15.

## Certified (exhaustive) negative results, and what w18 reproduced
- w11 exh3 (certified.tsv, split metacyclic groups, D = 9, minimum cost over all S = {e,x,y,z} up to Aut and translation):
  `cd w11 && ./exh3 meta M K R 100000 TAG 500 9` (or run_any.sh). w18 re-ran 26 split groups with the same binary in its own
  folder; every minimum matched: 101_25_5 = 2, 104_24_7 = 4, 208_12_3 = 4, 35_72_4 = 6, 105_24_17 = 6, 208_12_141 = 6,
  420_6_109 = 6, 70_36_9 = 8, 208_12_29 = 8, 208_12_37 = 8, 208_12_43 = 8, 208_12_11 = 9, 104_24_11 = 10, 35_72_3 = 10,
  105_24_2 = 10, 210_12_23 = 10, 210_12_79 = 10, 115_22_4 = 10, 215_12_92 = 10, 208_12_115 = 10, 52_48_7 = 12, 208_12_69 = 12,
  416_6_367 = 12, 105_24_52 = 12, 320_8_7 = 12, 427_6_13 = 12 (all 26 split rows in certified.tsv that are on or below 12).
  Non-split rows: re-ran 3 (`./exh3 tab tabs/ns_<tag>.bin 100000 <tag> 170 9`): ns_m208_k12_r3_s104 = 4, ns_m208_k12_r141_s52 = 6,
  ns_m210_k12_r17_s105 = 6, all matching. Their tables pass random associativity and identity checks (val/assoc_check.py).
  The other ns rows (6 to 12, 700-800 s each) were not re-run.
  Calibration of exh3 against brute force (w18/val/brute.c: every S, no symmetry): 9 cases (metacyclic groups of order
  110 to 156 with D = 3, 5, 7, 9), all minima equal (e.g. 15_8_2 D=5: 38 both; 13_12_2 D=5: 102 both; 15_8_2 D=3: 214 both).
- w1 exh (A_7, Haar graphs, class representatives of the 8 non-identity classes): min cost 6, zeros 0. Re-run of the class
  of element 19 (`cd w1 && ./exh tabs/A7.bin 6 5 6`): evals 3168903, best 6, identical to w1/res/exh_A7_class19.out.
  Other reps in w1/res: best 6 (c01, c23), 7 (c4, c67). Not re-run.
- w7 bicos exh (PSL(2,25), H of order 3, composition {1,3}, 6912 sets): C = 30. Recipe in w7/NOTES.md. w7's bicos was not
  re-run; w18 re-derived the same count (6912) and value (30) with w9's bi9 (see w9 below).
- w9 bi9 exh (bi-coset, exact minima per (G,H) class): M11 H3 = 38, S7 H=K2 = 15, PSL(2,25) H3 = 30, PGL(2,25) order-6 = 30.
  S7 K2 re-run by w18 (private copy, `CAP=2000000 ./bi9 runs/S7_h2_K2.bin exh 0 out.edges`, 273 s): {2,2} exhaustive
  (778,128 combinations) min 15; {2,1,1} exhaustive (344,448) min 44; {1,1,1,1} exhaustive (10,626) min 9,984. So 15 is the exact
  minimum for that class over all compositions. The edge list re-derived by w18 has far 18,900, diameter 10 (checked).
  Caveat: w9/results.tsv rows for S7 show evals=600000 (a smaller CAP). Only the CAP=2000000 recipe is exhaustive.
  PSL(2,25) H3 (class K0) re-run by w18 with bi9: {3,1} exhaustive, 6912 combinations, min 30; {1,1,1,1} exhaustive (70),
  min 10368. Same count and value as w7's independent bicos run ({1,3}, 6912 sets, C = 30, {1,1,1,1} gives 10368).
  M11 H3 (K0) re-run by w18: {3,1} exhaustive (10512) min 38; {1,1,1,1} exhaustive (495) min 10512. So 38 is exact.
  Recipe for both: `python3 grp9.py <G> 3 1500` (or build one class) then `CAP=2000000 ./bi9 runs/<tag>.bin exh 0 out.edges`.
  PGL(2,25) order-6 class: not re-run.
- w14 kbi exh (PSL(3,4), two subgroups of order 8, 9 classes x 81 pairs): minimum 312. w18 re-ran the (H3,K5) pair
  (`kbi runs/K_PSL34_h8_H3_K5_c0.bin exh 0 OUT`, 50 evaluations, 0.03 s): 312, as claimed. Other pairs not re-run.
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
