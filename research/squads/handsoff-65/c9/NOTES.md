# c9 notes: re-lift quotients of the 684 Haar graph

## Setup (done 16:30)
- groups/sg_342_12.txt: G = SmallGroup(342,12) = C6 x (C19:C3), table made by shared/gap_tables.g.
- Haar S = {113,16,280,65,59,295} (table indices, from c6 notes). g684.edges: H(G,S) = 684 vertices, check.sh bad=0 (valid).
- normals342.txt: the 16 normal subgroups (GAP). Lines used for quotient bases (1-based line numbers):
  5 C19 (base 18+18), 6 C38 (9+9), 7 C19:C3 (6+6), 10 C2x(C19:C3) (3+3), 13 C57 (6+6), 14 C114 (3+3), 15 C3x(C19:C3) (2+2).
  (Lines 8/9, 11/12 are the other conjugate copies of the same type.)
- src/quot.py GTAB S LINE BASE NTAB: quotient base (vl format, gauge-normalised to identity tree) and N's table.
  src/lift.py BASE TAB > edges: lifts a base by a table. All 7 quotient bases lift back to the 684 graph (bad=0).
- Calibration: tabu INIT=random on base_L13 (C57, 6+6) with 60 s: best 64 (not solved yet, see below).
- Tool timing: tabu ~4 steps/s on 12-vertex bases (slow). Use timeout 600000 in Bash for runs > 100 s.

## Calibration (16:30-16:37)
- vl SA on the 1+1 Haar base (6 parallel edges, random voltages) over SmallGroup(342,12): cost 0 (the 684 graph) in 8.7 s.
  So the annealer works. Base file: cal/base11_random.base.
- C57 quotient base (base_L13, 6+6): tabu from random: best 48 after 300 s (1350 steps, no restart fired);
  vl SA from random: best 46 in 60 s. The known 684 solution is NOT re-found from random starts on this base.
  Reading: the 684 structure is rare in this base; plateau cost ~46 at n = 684 with an abelian group.
- Tools chosen for scans: vl (about 4500 iters/s on the 12-vertex base; tabu runs ~4 steps/s, too slow).

## Scan (vl SA, SECS=20, ITERS=90000, random start by src/randbase.py, one run per group)
- driver: src/scan_vl.py TAG BASE ORDERS SECS ITERS SEED; chain: src/chain1.sh (bases L13 C57 6+6, L7 C19:C3 6+6,
  L5 C19 18+18, L6 C38 9+9). Results: runs/<TAG>.tsv (order, group id, name, best cost).
- Planned next: L14 (3+3, C114) by orders 115..120; L15 (2+2, C3x(C19:C3)) by 172..180; 1+1 is not mine (c5/c6).

## Scan status 16:40
- chain1 (src/chain1.sh): A_L13 (C57 6+6) orders 58-60: best so far C58 cost 82, C59 88, C60 107-112 (abelian best). Running B_L7, C_L5, D_L6 next.
- chain2 (src/chain2.sh, waits for chain1): E_L14 (3+3, C114) orders 115-120, A2_L13 orders 61-66, B2_L7 orders 61-66.
- summary: src/summary.sh prints the best five per runs/*.tsv.

## Results 16:49
- A_L13 (C57 quotient, 6+6), orders 58-60 (16 groups, 20 s vl SA each): best C58 cost 82, C59 88, C30xC2 92.
- B_L7 (C19:C3 quotient, 6+6), orders 58-60: best C3x(C5:C4) 84, C59 92, C58 96.
- Lift check: runs/A_L13_58_2.base lifted (src/lift.py) gives n=696, bad=2378 (check.sh-style count). Edge list best_n696_C58.edges.
  Scoreboard line appended (first personal best at n=696).
- Queue (src/chain1.sh -> src/chain2c.sh): C_L5 (18+18, orders 20-22), D_L6 (9+9, 39,40,42), then F_L15 (2+2, 172-180,
  12 s each), E_L14 (3+3, 115-120, 12 s), then src/longrun.py 8 200 1 (best 8 rows over all runs, 200 s SA each).
- Calibration status: C57 base does not re-find the 684 from random (SA cost plateau 46 at 60 s); the 1+1 base does (8.7 s).

## 2+2 scan (F_L15, base = quotient of the 684 graph by C3x(C19:C3), orders 172-180, 94 groups, 12 s each), 17:18
- best vl costs: C174 (SmallGroup(174,4)) 12; C2x(C11:Q8) (176,27) 14; C11:(C4:C4) (176,12) 16; C29xS3 17.
- n=696 lifts: C174 bad=1044 (best_n696_F174_C174.edges, scoreboard line appended); C29xS3 bad=1479.
- Costs for 2+2 bases are much smaller than for 6+6 (4 base vertices), so compare bad pairs, not costs, across bases.
- Long runs (src/longrun.py 6 180 1, top 6 rows) started 17:18; then the 3+3 scan E_L14 (src/chain2d.sh).

## 17:27 status
- longrun with ITERS=1e8 was a mistake (the annealing schedule never cools inside SECS); stopped it after one result (C174 seed 1004: cost 16).
- Multi-seed short anneals (src/ms.py, 15 s, ITERS 60000, base F_L15) on the top 8 2+2 groups: C174 gives 18-27 across seeds;
  the earlier 12 (12 s run, seed 1) is a lucky tail. Typical cost ~20 for the best groups.
- Queue (chain4): tabu 300 s on the C174 2+2 best (runs/tabu_174_4_s1.*), then 3+3 scan E_L14 (12 s each).
- 17:37: multi-seed 2+2 (src/ms.py, 6 seeds x 15 s on 8 groups): best cost 12 for C11xQ16 (176,26) and C174 (12 earlier).
  n=704 lift of the C11xQ16 cost-12 solution: bad=1056 (best_n704_C11Q16.edges); scoreboard line appended (first n=704 entry).
