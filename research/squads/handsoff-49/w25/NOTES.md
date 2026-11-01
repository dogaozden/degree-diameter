# w25 NOTES: final auditor and summary table (handsoff-49, follows w18)

Start: 02:00 UTC (card: part 1 until 02:57, part 2 02:58 to 03:10, reply in at most 5 lines).
Files: audit2.tsv (scoreboard lines added after the w18 audit, index > 51), build_audit2.py (regenerates it),
raw/ (score48 and apsp output per edge file), summary.md (part 2).

## Log
- 02:00 started. Scoreboard has 51 data lines (w18 audit covered all 51 at 01:57). Nothing new yet.
- 02:04 independent re-check (w25/indep_bits.py: bitset reach sets, no tools code, plus tools/score48 and tools/apsp)
  of all 51 scoreboard lines (w25/indep_all.tsv, build_audit2.py 1): 37 edge-list files, all agree with score48 (n,
  degree, diameter, far pairs). Only VALID at d=4 D=9: line 7 (w3, n=3200) and line 48 (w16, n=4970 rebuild). None > 4970.
  Other lines are not edge lists or have no file (see the table in indep_all.tsv).
- Discrepancy found in w18/audit.tsv: line 7 cell score48_apsp = INVALID, but tools/apsp and tools/score48 print
  RESULT VALID at D=9 for w3/runs/rep40b_c0.edges (n=3200). INVALID is the D=8 result (apsp at D=8 gives INVALID, as
  expected). The row verdict text says VALID, so only the cell is wrong.
- Re-checks of w18's rebuilt files with w25/indep_bits.py: w18/val/hb1_c.edges (n 5000, diam 10, far 12500),
  u4m7_c.edges (n 5000, diam 10, far 5000), w23chk_a.edges (n 5000, diam 10, far 5000) agree with w18.
  w18/val/w23chk_b.edges is DISCONNECTED (4 components, not on the scoreboard; not a candidate).
- Scoreboard lines per worker: w1 3, w10 1, w11 16, w12 3, w13 1, w14 1, w15 2, w16 2, w17 1, w2 2, w23 1, w3 2, w4 4,
  w5 4, w6 1, w7 1, w8 4, w9 2 (total 51). No lines from w18-w22, w24 (at 02:04).
- Stale claim: w8's lines 3, 8, 15 (claims 24, 18, 16) and line 17 name w8/runs/w8_best_n4992.edges; the file now gives
  far 9360 (cost 15), the w8 final value. Lines 3, 8, 15 cannot be reproduced from that path.
- w17 NOTES.md stops at 00:55 (11 lines) but the scoreboard has w17's 01:50 line (A7 mixed orbit, far 15120).
- w22 and w24 have no NOTES.md at 02:04 (folders written 01:57-01:59).
- 02:06 w24 benchmark (from its logs and files, no NOTES.md yet): 5+5 base over meta:71:7:45 from random voltages reached
  cost 0 (FOUND) in 0.5 to 7 s on 4 of 10 seeds (k=5 log). Logs also show FOUND for labels k=25 (3 of 10), k=54 (3 of 10),
  k=57 (3 of 10). Checked by apsp (D=9) and w25/indep_bits.py: w24/bench_k5_s1, bench_k5_s9, bench_k25_s1, bench_k54_s2,
  bench_k57_s1, symk5, symk25, symk57 are all VALID at n=4970 (the known table value). Not a record.
- 02:08 re-run of one w20 certified row in a private copy (w25/chk, binary copied from w20/exh3):
  `exh3 meta 1243 2 1242 1 w25chk_m1243 300 9` (LIMIT 1, N=2486) finished with the same evaluation count as w20
  (864032), wrote no out/*.edges (so no set of cost <= 1), state "done 1". w20's row "DONE, no cost-0, min >= 2" holds.
  Note: LIMIT 1 proves only "no set of cost <= 1", not an exact minimum.
- 02:10 w23 exhaustive tally re-done from its output files (no re-run): runs_rep0.txt, runs_reps1_7.txt, runs_reps8_13.txt
  contain 14 histograms of 3,118,753 sets each (= C(2498,2) per representative, 43,662,542 in total). Cost histogram:
  cost 4: 1,160 sets, cost 5: 0, cost <= 3: 0, cost 6 or more: 40,542,629 (the file caps the bucket at 6). Minimum 4 over
  the 14 representatives, as claimed. Orbit sizes in aut_orbits.txt (14 rows) sum to 2499 = |G| - 1; the multiset is
  {1, 4, 4, 20, 20, 50, 100, 100, 100, 100, 200, 400, 400, 1000}. The list in w23/NOTES.md (three 100s, sum 2400) is a typo.
  Aut(G) itself (order 20000) and the orbit computation were not re-derived.
- 02:09 the Write of w25/summary.md was refused by the tool ("Subagents should return findings as text"). The summary
  will be returned as text in the SubagentHandback report instead. No other report file is written.
- 02:09 audit2 (scoreboard lines 52 and up): none yet (scoreboard still 51 data lines).
- 02:10 independent check of w4's girth fact (w25/girth_check.py on seeds/hexagon_q3.json): 728 vertices, 4-regular,
  girth 12, diameter 6. With the covering argument (a shortest lift path to another fibre point projects to a closed
  non-backtracking walk, which has length >= girth), every lift of H(3) has diameter >= 12. Holds.
- 02:11 re-runs of w11's certified rows (copy of w11/exh3 in w25/chk, LIMIT = cost bound, D = 9):
  meta 104 24 7 with LIMIT 3: DONE, no set of cost <= 3 (no edge file written), 3,989,737 evaluations, 47 s. Confirms w11's
  exact minimum 4 (cost-4 set exists: line 39, far 4992 verified).
- 02:12 meta 208 12 3 with LIMIT 3: DONE, no set of cost <= 3 (2,316,009 evaluations): confirms w11's exact minimum 4.
- 02:10 meta 101 25 5 with LIMIT 1: DONE, no set of cost <= 1 (806,175 evaluations): confirms exact minimum >= 2 (cost-2 file line 21 verified).
- 02:12 meta 105 24 17 with LIMIT 5: DONE, no set of cost <= 5 (3,207,758 evaluations): confirms w11/w18 exact minimum >= 6.
- 02:13 audit2 (scoreboard lines 52..54, all from w22 at 02:09): 52 calibration n=4970 VALID (not a record, claim holds);
  53 cc7 n=5096 far 81619 diameter 11 (claim holds); 54 mx_m104_a1 n=4992 far 25776 diameter 10 (claim holds). None VALID > 4970.
  Scoreboard now header + 54 data lines. Note w17 has also written a newer file (A7_r4444_133_deep.edges, far 15120,
  same value as line 51) that has no scoreboard line.
- 02:13 meta 208 12 141 with LIMIT 5: DONE, no set of cost <= 5 (2,680,038 evaluations): confirms lower bound 6 (w11 min 6).
- 02:13 meta 208 12 11 with LIMIT 8: DONE, no set of cost <= 8 (1,685,982 evaluations): confirms lower bound 9 (w11 min 9).
- 02:14 meta 104 24 11 with LIMIT 9: DONE, no set of cost <= 9 (3,269,125 evaluations): confirms lower bound 10 (w11 min 10).
- 02:15 audit2 (scoreboard lines 55, 56, both new since 02:12):
  55 w23 (02:13) mz5_6 (|Aut| = 10000, 34 orbit reps): "no set with cost <= 5". w25 re-tallied w23's files
     runs_mz5_reps0_6, _reps7_14, _reps15_22, _reps23_29, runs_mz5_rep30..33 (all 34 reps): 34 histograms of 3,118,753 sets
     (106,037,602 in total), costs 0..5 all zero, the rest in the cap bucket 6. Claim holds (min >= 6 for this group).
     Aut(G) not re-derived. Not a record.
  56 w24 (02:13) Z_5-symmetric voltage SA (volt(sigma e) = phi(volt e)) on 5+5 over meta:71:7:45: 13 of 40 runs cost 0.
     Rebuild w24/symk5.edges VALID at n = 4970 (checked by w25 earlier). Claim holds. So the w24 labels k=5/25/54/57 are
     the SYM_k symmetric searches (phi(x)=x^k), not plain random-voltage annealing. The benchmark of the card is met only
     under this imposed Z_5 symmetry, not for plain SA.
  Scoreboard now header + 56 data lines.
- 02:15 clarification: the w24 scoreboard line 56 states the Z_5-symmetric SA. The benchmark logs name SYM labels only; I
  found no log of a non-symmetric (plain) run that reaches cost 0, so the card's plain-SA benchmark is not shown met.
- 02:16 full scan of every *.edges file in the squad folders (w25/scan_edges.py, resumable, results in scan_edges.tsv):
  1,493 files. 95 skipped (n <= 4970). The other 1,398 files (4,972 <= n <= 8,160) all ran through tools/apsp at d=4 D=9:
  1,130 INVALID (diameter), 268 INVALID (disconnected), 0 VALID. So no edge file in the squad is a record, including files
  that have no scoreboard line. Formats other than .edges (.sol, .volt, .bin, .txt) were not scanned.
- 02:19 w20 DONE row m25_k100_r2 (N=2500) re-run by w25 in three resumed segments (exh3 binary copy, LIMIT 1, 129 reps):
  DONE, no set of cost <= 1 (no edge file written). Confirms w20's ">= 2".
- 02:19 w20 certificate.tsv now has 38 rows: 15 DONE (no cost <= 1, i.e. min >= 2) and 23 covered_by_w11.
- 02:21 LIMIT 7 re-runs: meta 208 12 43 (DONE, 1,884,133 evals) and meta 208 12 29 (DONE, 3,723,163 evals): no set of cost <= 7, lower bound 8 confirmed (w11 min 8).
- 02:21 meta 208 12 37 LIMIT 7: DONE, no set of cost <= 7 (2,680,038 evals): lower bound 8 confirmed.
- 02:24 meta 70 36 9 LIMIT 7: DONE (two segments, 119 reps), no set of cost <= 7: lower bound 8 confirmed (w11 min 8).
- 02:25 meta 105 24 2 LIMIT 9: DONE, no set of cost <= 9 (3,588,742 evals): lower bound 10 confirmed (w11 min 10).
- 02:25 meta 210 12 23 LIMIT 9: DONE, no set of cost <= 9 (2,450,006 evals): lower bound 10 confirmed (w11 min 10).
- 02:27 meta 210 12 79 LIMIT 9: DONE, no set of cost <= 9 (3,555,307 evals): lower bound 10 confirmed (w11 min 10).
- 02:29 meta 35 72 3 LIMIT 9 (two segments, 107 reps): DONE, no set of cost <= 9: lower bound 10 confirmed (w11 min 10).
- 02:29 meta 416 6 367 LIMIT 11: DONE, no set of cost <= 11 (1,053,761 evals): lower bound 12 confirmed (w11 min 12).
- 02:31 meta 52 48 7 LIMIT 11 (two segments, 107 reps): DONE, no set of cost <= 11: lower bound 12 confirmed (w11 min 12).
- 02:31 meta 427 6 13 LIMIT 11: DONE, no set of cost <= 11 (324,771 evals): lower bound 12 confirmed (N = 2562, w11 min 12).
- 02:32 meta 320 8 7 LIMIT 11: DONE, no set of cost <= 11 (1,913,065 evals): lower bound 12 confirmed (N = 2560).
- 02:33 meta 105 24 52 LIMIT 11: DONE, no set of cost <= 11 (2,657,306 evals): lower bound 12 confirmed (w11 min 12).
- 02:33 meta 208 12 69 LIMIT 11: DONE, no set of cost <= 11 (2,878,189 evals): lower bound 12 confirmed.
- 02:36 meta 35 72 4 LIMIT 5 (two segments, 143 reps): DONE, no set of cost <= 5: lower bound 6 confirmed (N = 2520).
- 02:37 meta 420 6 109 LIMIT 5: DONE, no set of cost <= 5 (2,096,240 evals): lower bound 6 confirmed (N = 2520).
- 02:37 meta 420 6 109 done above. Repeat of meta 105 24 17 LIMIT 5 gave the same 3,207,758 evaluations (reproducible).
- 02:38 meta 208 12 115 LIMIT 9: DONE, no set of cost <= 9 (1,685,982 evals): lower bound 10 confirmed (w11 min 10).
- 02:39 meta 215 12 92 LIMIT 9: DONE, no set of cost <= 9 (718,677 evals): lower bound 10 confirmed (N = 2580, w11 min 10). SUMMARY OF w25 RE-RUNS of w11 exh3 (copy of w11/exh3, LIMIT = claimed min - 1): 26 split groups, every DONE with no set below the claimed minimum: 101_25_5 (L1), 104_24_7 (L3), 208_12_3 (L3), 105_24_17 (L5), 208_12_141 (L5), 208_12_11 (L8), 104_24_11 (L9), 416_6_367 (L11), 52_48_7 (L11), 427_6_13 (L11), 320_8_7 (L11), 105_24_52 (L11), 208_12_69 (L11), 208_12_43 (L7), 208_12_29 (L7), 208_12_37 (L7), 70_36_9 (L7), 105_24_2 (L9), 210_12_23 (L9), 210_12_79 (L9), 35_72_3 (L9), 208_12_115 (L9), 215_12_92 (L9), 35_72_4 (L5), 420_6_109 (L5). Attainment (a set of the claimed cost exists) checked by an edge file only for 101_25_5 (cost 2, line 21), 104_24_7 (cost 4, line 39) and 208_12_3 (cost 4, line 23).
- 02:45 meta 1245 2 1244 LIMIT 1 (w20 DONE row, N=2490): DONE over 8 reps (three segments, 1,564,230 evals in total), no set of cost <= 1 (no edge file). Confirms w20's >= 2. Note: a single call with MAXSEC 90 was killed by the 100-s timeout twice; resume with MAXSEC 30 works.
- 02:47 meta 1247 2 1246 LIMIT 1 (w20 DONE row, N=2494): DONE, no set of cost <= 1 (2 segments). Confirms w20's >= 2.
- 02:50 meta 1249 2 1248 LIMIT 1 (w20 DONE row, N=2498): NOT completed by w25. The first repetition takes more than 100 s, so no state was saved (two calls killed by the timeout). Row left as w20 reported it.
- 02:51 audit2 line 57 (w23 02:45, mz5_6, all 34 Aut-orbit reps, cap 9): w25 checked the logs cap9_mz5_*.err: each of the 34
  reps reports "done (3118753 sets)"; every histogram line in the cap9 .err/.txt files has zero entries for costs 0..8
  (48 histogram lines, 0 nonzero below 9). So no set of cost <= 8, lower bound 9 confirmed for this group. The annealing
  value 10 (upper side) is not checked. Also note the w23 cap-6 files (line 55) are consistent: all sets >= 6.
- 02:52 w21 exact.tsv rows: S5xF21 exact 8 (complete); u4m_7 partial (6 of 123 reps, floor 4 found); A5xS3xZ7 partial (53 of 104 reps, >= 9 on covered reps); PSL(2,8)xZ5 running (reps 23..43 done, best 8). w18 audit.tsv and NOTES.md last written 01:56 (its 02:10 and 02:30 re-audits not in its files).
- 02:52 w6 claim re-checked: deleting one edge of seeds/valid4970.edges (edge (0,2485)) gives far unordered 179 (diameter 11), as w6 says.
- 02:53 meta 25 100 2 with LIMIT 0 (cost-0 existence, N = 2500, 129 reps, resumed in three segments): DONE, no set of cost 0 (no edge file). Consistent with the LIMIT 1 result.
- 02:54 (aborted, not a result): exh3 meta 105 24 7 failed with 'no inverse' because r=7 is not a unit with r^24 = 1 mod 105; no conclusion drawn.
- 02:55 meta 35 72 4 LIMIT 3 (143 reps, redundant with LIMIT 5): DONE, no set of cost <= 3.
- 02:56 LOC recount (.c + .py, wc -l, excluding binaries): w1 1785 (1214 without the 571 lines of verbatim tools copies), w2 103,
  w3 1266, w4 2386, w5 617 (431 without flift.c copy), w6 772, w7 1128, w8 623, w9 942, w10 344, w11 834, w12 672, w13 554,
  w14 1170, w15 829, w16 830, w17 837, w18 1804, w19 1103, w20 762, w21 168, w22 385, w23 1116, w24 855, w25 189.
- 02:57 notes read: w22 NOTES (01:23 to 02:55): no record; compound 5,096 far 81,619; mixed 4,992 far 25,776; semidirect
  p=17 k=9 (n 5,202) far 36,414 (the file w25 checked); dead ends listed. w24 NOTES (01:31 to 02:55): plain SA lo.c 0 of 3
  runs reach cost 0 (best 70 to 78); Z_5-symmetric sym.c 13 of 40 reach cost 0 (all VALID n = 4,970). w21 NOTES: A5 x S3 x Z7
  reps 0..55 done, first cost 8 at rep 55, no cost below 8 in reps 0..55 (partial). w23 NOTES: cap-10 run on mz5_6 planned to decide 9 vs 10.
  w17 NOTES (to 02:43): A7 (4,4,4,4) floors at 15,120 far pairs; extra seeds 17,955 to 20,160.
- 02:57 w21 exact.tsv: PSL(2,8) x Z5 (order 2520, centre 5) EXACT minimum 8 over all 44 non-identity class reps (20 sets of cost 8, none below). S5xF21 exact 8. u4m_7 partial (6 of 123 reps, no cost below 4 there). A5xS3xZ7 partial (reps 0..55 of 104; 8 first seen at reps 53..55; not certified).
- 02:56 full re-run of the independent check on all 57 scoreboard lines (edge files as they are now): no line changed compared with the 02:01 run; VALID lines: 7, 48, 52, 56 (none above 4970).
- 02:58 part 2 started. m1249 re-run again killed (first rep > 100 s), not verified by w25.
- 02:59 extra LIMIT-5 segment for 35 72 3 (redundant, stopped; LIMIT 9 result stands).
- 03:00 part 2 status: scoreboard 57 data lines (no change since 02:55), audit2 covers lines 52-57, scan 1,532 edge files (1,408 checked, all INVALID; 124 skipped n <= 4970). Final report via SubagentHandback at about 03:05 (summary.md write refused by the tool).
w20 row m1249 reports DONE in 142 s (its own log); w25 re-run did not finish within 100-s calls.
- 03:03 final state: scoreboard 57 data lines, all re-checked (w25/indep_all.tsv, unchanged since 02:01 for lines 1-51); audit2.tsv lines 52-57 (no VALID above 4970); scan_edges.tsv: 1,532 .edges files, 1,408 INVALID for n 4972..8160, 124 skipped (n <= 4970). Report handed back at 03:04.
