# r2b notes (mixed and hubs screens)

Tools: copies of tools/mixed.c and tools/hubs.c (gcc -O3 -march=native), unchanged. Tables: r1/c1/g/*.tab (symlinked
for A5x_C7C6, A7, A5xC3xD7); SmallGroups and non-solvable hub groups via GAP (`exp_b.g`, `sg2.g`, ExportNoAut, then
build_tab.py); metacyclic via `mktab.py m k r PREFIX` (table only). Candidate lists: `cands.py mix|hub`.
Runners: `runmix.sh NAME CPU SEED`, `runhub.sh NAME CPU SEED` (append to results.txt; edges in runs/).

Results (screen cost, lower is better; 0 would mean diameter <= 9). Best per group is in the scoreboard (44 lines, card r2b).
- mixed, best: Z_125 x|_7 Z_20 = 17; Z_115 x|_14 Z_22 = 18; A5 x (C7:C6) = 19; A7 = 21 (calibration
  matches the director's value); A5 x C3 x D7 = 23; A6 x C7 = 26. Dihedral-type SmallGroups (abelianisation C2) are
  about 6500 (near the maximum).
- hubs, best: PSL(2,7) x A4 = 25 (2016, n 5040); PSL(2,8) x C4 = 29; Z_101 x|_32 Z_20 (2020) = 32; next Z_175 x|_18 Z_12 = 75; the rest >= 128 or near the maximum.
- Verified with score48 (both are not valid): hub PSL(2,7)xA4 graph: diameter 10, 16884 far pairs; mixed Z_125 x| Z_20
  graph: diameter 10, 18125 far pairs. No cost-0 result, so no apsp run is needed.

Coverage (not complete): mixed on the 10 r1 non-solvable tables, 7 of about 50 SmallGroups of order 2486..2600 with >= 10
non-central involutions, 5 of about 660 split metacyclic candidates. Hubs on all 12 SmallGroups of orders 1992..2100 (4 | n)
with |G/G'| <= 309, 4 non-solvable groups, 6 of the metacyclic candidates. Seeds: mixed seeds 2 and 3 on the top 4-5 groups (10 CPU s);
hubs seeds 2 and 3 on the top 5 (8 CPU s).
Mixed seeds were 10-15 CPU s (first pass 15, seed 1 on the r1 tables 30 CPU s). Each run ~1.5x its CPU time in wall time.
