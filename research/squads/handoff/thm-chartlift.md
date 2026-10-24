# Handoff: job thm-chartlift (round 3 session, branch claude/chartlift-family-h3605i)

Written during the session so a resume can pick up if this session is cut off. Main write-up:
research/theorems/CHART_LIFTS.md (Results first table, Lemma 5, Theorem 11, Proposition 12). Round-3 files:
research/theorems/chartlift/r3/ (graphs/, diag43/, charts k*q*_*.txt, run logs).

## Verified new records (builders + apsp/bfs_all check files in chartlift/r3/graphs/)
- (15,5) 25,272: Haar graph of Z26 x|3 Z6 (m=156), chart r3/k5q3_pd112.txt.
- (12,5) 11,664: K3,3 + doubled matching over Z3 x|2 Z8 (m=72), chart r3/k4q3_diag_cls1.txt (squad r3 card c2). Also 10,368 (Haar Z16 x|3 Z4).
- (10,5) 4,032: Haar graph of Z14 x|9 Z9 (m=126), chart charts/r2_k5_q2.txt (squad r2 card c4).
None of these is recorded by the coordinator yet (as of this note).

## Key idea
Charts that cover both diagonals + complete pencils => controllers need no 4-cycles => Haar graphs of metacyclic
groups work. Chart conditions depend only on points w_c, b_c and the star collineations (Lemma 5); search those
(r3/chart_anneal3.c MOVES=star, r3/diag43/*).

## Open leads (as of writing)
- (15,5): m=160 reaches cost 2 (meta:20:8:13, chart r3/k5q3_pd102.txt). Better (5,3) charts (fewer than 102 singular).
- (12,5): Haar m=66..78 stall at cost >= 2 for all 7 chart classes (r3/k4q3_diag_cls*.txt); exhaustive scan
  r3/exh_d12.sh -> r3/exh_d12.log over orders 65..81. Try 2+2 / 3+3 bases.
- (10,5): m=128 reaches cost 1 (squad c5). Better (5,2) charts.
- (8,5): Haar exhaustive over orders 60-81 fails with the 48-singular (4,2) chart (squad c6); needs a sparser (4,2) chart.
- (14,5), (12,5) via 6xF2: charts too singular (43%, 40%).
