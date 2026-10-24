# Handoff: job thm-chartlift (round 3 session, branch claude/chartlift-family-h3605i)

Main write-up: research/theorems/CHART_LIFTS.md (Results first table; Lemma 5, Theorem 11, Propositions 12-13,
Theorem 14; ranked sections). Round-3 files: research/theorems/chartlift/r3/ (graphs/, diag43/, dpmin/, cdesc/,
flags43/, alt/, run logs). Squad rounds r2-chartlift and r3-chartlift are logged in research/squads/LOG.md.

## Verified new records (self-contained builders + apsp/bfs_all check files in chartlift/r3/graphs/)
- (15,5) 27,216: Haar graph of Z28 x|11 Z6 (m=168; connection set from squad r3 card c4), chart r3/k5q3_for168.txt
  (re-optimised for this controller by r3/cdesc/star_cd_ctrl.py). Earlier this session: 25,272 and 22,680.
- (12,5) 12,960: base [[1,3],[3,1]] over Z5 x|2 Z8 (m=80; base/group from squad r3 card c1), chart
  r3/k4q3_diag_s126.txt (closed by r3/alt348.sh). Earlier: 12,150, 11,664, 10,368.
- (10,5) 4,480: Haar graph of Z35 x|29 Z4 (m=140; group from squad r3 card c6 at cost 4), chart r3/k5q2_for140.txt
  (r3/alt_opt.sh: voltages cost 4, then the chart descent reached cost 0 in 8 s). Earlier: 4,096 (Z32 x|9 Z4 and
  Z16 x|5 Z8, m=128, charts r3/k5q2_for128a.txt, ...b.txt, same method) and 4,032 (Haar graph of Z14 x|9 Z9, m=126; squad r2 card c4, chart charts/r2_k5_q2.txt).
None of these is recorded by the coordinator yet (as of this note).

## Key ideas
1. Charts covering both diagonals + complete pencils => controllers need no 4-cycles (Theorem 11).
2. All D=5 chart conditions depend only on the points w_c, b_c and the star collineations (Lemma 5): search those
   (r3/chart_anneal3.c MOVES=star, r3/cdesc/star_cd.py), and classify small cases exhaustively (r3/diag43, r3/dpmin).
3. Near misses are closed by re-optimising the chart for the fixed controller (r3/cdesc/star_cd_ctrl.py, r3/alt_opt.sh);
   at (4,3) the 348 labelled singular sets are finite (r3/flags43), so score them all (r3/alt348.sh, r3/score348.sh).

## Open leads
- (15,5): alternating optimisation running/ran over orders 171-180 (r3/alt/d15_*.log). Best known (5,5) graph has
  m = 177, so (15,5) <= about 28,674 by this route.
- (12,5): m=80 is 99% of the (4,5) record's m=81; m=82 attempts (Z41) cost 12-20.
- (10,5): m=140 done (4,480). Next: orders 144-160 with r3/alt_run10b.sh (screen 90 s, alternate if cost <= 8).
- (8,5): (4,2) charts are optimal at 48 singular; 2+2 near miss at m=66 (Z33) being tried with r3/alt_opt.sh.
- (14,5): (7,2) charts ~42% singular; Haar m=462 cost 36. Needs a different idea.
