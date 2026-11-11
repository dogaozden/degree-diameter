# w25 summary (handsoff-49 final auditor)

Written by the coordinator from w25's final reply: the Write tool refused the file for the subagent, so w25 returned it
as text. Working files: w25/NOTES.md, audit2.tsv, indep_all*.tsv, scan_edges.tsv, chk/.

## Audit
- All 57 scoreboard data lines re-checked with tools/score48, tools/apsp and w25/indep_bits.py (own bitset reach sets).
  Edge files agree on n, degree, diameter and far pairs. Re-run at 02:01 and 02:56, no change.
- Edge scan: all 1,532 .edges files in the squad (to 03:03). 124 have n <= 4,970. The other 1,408 (4,972 <= n <= 8,160)
  are all INVALID: 1,140 by diameter, 268 disconnected. Other formats (.sol, .volt, .bin, .txt) not scanned.
- VALID lines: only n = 3,200 (w3) and rebuilds of the n = 4,970 table graph (w16, w22, w24).
- Discrepancies: (a) w18/audit.tsv line 7 cell says INVALID, the file is VALID at D = 9 (INVALID is its D = 8 result);
  (b) w18's files stop at 01:56; (c) w8 lines 3, 8, 15 point to a file later overwritten (now cost 15 / far 9,360);
  (d) w15 lines 38, 46 say n = 2,500: the group has order 2,500, the Haar graph n = 5,000; (e) w23 NOTES orbit list typo
  (aut_orbits.txt is right, sum 2,499 = |G| - 1); (f) w2 has no edge file for its cost-2 and cost-4 results (w11's
  files cover the same groups).
- Re-runs of certified claims (copies of w11/exh3 and w20/exh3 with LIMIT = claimed minimum - 1): 26 w11 split groups,
  no set below the claimed minimum; attainment checked by edge file for 101 25 5 (2), 104 24 7 (4), 208 12 3 (4). w20
  rows m1243, m1245, m1247, m25 k100 r2: no set of cost <= 1. w23 u4m_7: 14 reps, 43,662,542 sets, minimum 4 (1,160
  sets), none below; mz5_6: no set of cost <= 8 (lower bound 9).
- Facts checked: H(3) incidence graph girth 12, diameter 6 (girth_check.py); |4D| = 309 in Z^3 (bound_check.py);
  deleting one edge of the valid 4,970 graph gives 179 far pairs.

## Per worker (best at n > 4,970: cost / far pairs; certified results)
- w1 Haar non-metacyclic: 5,040 A_7 cost 6 / 7,560. A_7 exhaustive minimum 6.
- w2 Haar metacyclic sweep: 5,050 cost 2 / 2,525; 4,992 cost 4.
- w3 W(3) lifts: 5,040 cost 906 / 28,539; valid only at 3,200.
- w4 H(3), PG(2,3), random 6+6 lifts: 4,992 cost 76 / 15,808. H(3) lifts have diameter >= 12 (girth 12).
- w5 2+2..4+4 lifts: 4,992 cost 4 / 2,496; 3+3 cost 19 / 7,904.
- w6 surgery: 4,972 / 160 far pairs (lowest far count above 4,970 in the squad).
- w7 bi-coset: 5,200 PSL(2,25) cost 30 / 39,000, exact.
- w8 2+2 lifts: 4,992 cost 15 / 9,360.
- w9 bi-coset simple groups: 5,040 S_7 cost 15 / 18,900, exact; M_11 38, PSL(2,25) 30, PGL(2,25) 30.
- w10 centreless Haar groups: 5,040 S_5 x F_21 cost 8 / 10,080 (exact by w21).
- w11 exh3 certification: 101 25 5 = 2, 104 24 7 = 4, 208 12 3 = 4 and 30 more exact.
- w12 simple-group lifts: 5,280 PGL(2,11) 2+2 cost 64 / 42,240.
- w13 cost-4 wall: 4,992 cost 4 / 4,992 (analysis, not a proof).
- w14 bi-coset large simple groups: 5,040 PSL(3,4) cost 312 / 393,120 (diameter 11), exact over 81 pairs.
- w15 P x| Z_4, order 2,500: 5,000 cost 4 / 5,000.
- w16 quotient lifts: 5,040 cost 82 / 20,664.
- w17 mixed-orbit A_7: 5,040 / 15,120.
- w18 auditor: lines 1-51.
- w19 refinement ladder: no improvement over the Haar starts.
- w20 metacyclic certificate 2,486..2,520: 69 rows (46 with no set of cost <= 1, i.e. minimum >= 2; 23 from w11).
- w21: S_5 x F_21 exact 8 (34 reps); PSL(2,8) x Z_5 exact 8 (44 reps); u4m_7 and A_5 x S_3 x Z_7 partial.
- w22 wildcard: compound 5,096 / 81,619; mixed bi-Cayley 4,992 / 25,776; a file at 5,202 / 36,414.
- w23: u4m_7 exact 4; mz5_6 >= 9.
- w24: plain SA 0 of 3 on the 5+5 benchmark; Z_5-symmetric SA 13 of 40.

## Lines of code (.c + .py)
w1 1,785 (1,214 without verbatim copies of tools), w2 103, w3 1,266, w4 2,386, w5 617, w6 772, w7 1,128, w8 623, w9 942,
w10 344, w11 834, w12 672, w13 554, w14 1,170, w15 829, w16 830, w17 837, w18 1,804, w19 1,103, w20 762, w21 168, w22 385,
w23 1,116, w24 855, w25 189. Total about 22,000 lines.
