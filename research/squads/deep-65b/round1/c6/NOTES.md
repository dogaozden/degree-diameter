# c6 notes (deep-65b round 1, wildcard)

## Construction: 4+4 voltage lifts (bipartite base with 4 A-vertices, 4 B-vertices)
- Base: 4x4 matrix M with row and column sums 6 (M_ij parallel base edges A_i-B_j). Group G of order m, n = 8m.
- Voltages: for each (i,j) with M_ij > 0 a set V_ij of M_ij distinct elements of G.
- Edges: (A_i,g) ~ (B_j, g*v) for v in V_ij. Lift is simple, bipartite, 6-regular.
- Left multiplication by G is an automorphism group acting regularly on each sheet, so only the 8 sheet identities need a BFS.
- Smallest m with n > 684 is m = 86 (n = 688). Groups of order 86: C86 (abelian, skipped), D86 = D43 = SmallGroup(86,2).
- Why this is not in the other cards: 2+2 (c1, c2), 3+3 (c5) and hub families (c3, c4). Here the base is 4+4 and the group is small.
- Walk-count check: from one base vertex, non-backtracking walks of length <= 4 total at most 6*5^3 + 6*5 + 1 = 781 over the
  4 same-side targets, so each target needs >= 86 (average about 195): the walk count is not binding at m = 86.

## Code: lift48.c (compiled: gcc -O3 -march=native -Wall -o lift48 lift48.c -lm)
- Cost S = sum over the 8 sheet identities of #vertices at distance > 5. Bad unordered pairs = m*S/2 = 43*S (m = 86).
- Simulated annealing on single voltage changes; T0 = 3, T1 = 0.12 in units of S over 150k-iteration epochs, restarting each
  epoch from the best state (env T0, T1, EPOCH override). Optional 6th argument: start from a saved .volt file.
- Output: OUTPREFIX.edges (score65 format) and OUTPREFIX.volt.

## Groups
- gapw -c 'ORDER:=86; OUTDIR:="tabs";' tools/gap_tabaut.g (in shared/gapw, inside this folder)
- gapw -c 'ORDER:=90; OUTDIR:="tabs";' ...   (10 groups)
- gapw -c 'ORDER:=88; OUTDIR:="tabs";' ...   (only 12 of 51 groups written before the 100 s limit; D88 = sg_88_5 used)

## Calibration (cost vs scorer, random states on D43, base B1)
- ./lift48 tabs/sg_86_2.tab 3,1,1,1,1,3,1,1,1,1,3,1,1,1,1,3 1 -1 cal_1, then score65 cal_1.edges: 16340 = 16340
- seed 2: 12212 = 12212; seed 3: 14362 = 14362. Exact match.

## Runs (85 s each, one at a time, single thread; B1 = 3 on diagonal, 1 off; B2 = [[2,2,1,1],[1,2,2,1],[1,1,2,2],[2,1,1,2]];
## B3 = [[2,2,2,0],[2,2,0,2],[2,0,2,2],[0,2,2,2]]; B4 = [[3,3,0,0],[3,1,1,1],[0,1,2,3],[0,1,3,2]])
| run | group, base | start | bad pairs | S | iterations |
|---|---|---|---|---|---|
| run_d43_b1_s1 | D43, B1 | random, seed 1 | 1935 | 45 | 196k |
| run_d43_b1_s1b | D43, B1 | from s1, seed 2 | 1505 | 35 | 439k (best) |
| run_d43_b1_s6 | D43, B1 | from s1b, seed 6 | 1505 | 35 | 468k (no gain) |
| run_d43_b1_s7 | D43, B1 | from s1b, T0=1, T1=0.2, EPOCH=60000 | 1505 | 35 | 456k (no gain) |
| run_d43_b1_s10 | D43, B1 | random, seed 10 | 2322 | 54 | 190k |
| run_d43_b2_s3 | D43, B2 | random, seed 3 | 1634 | 38 | 463k |
| run_d43_b2_s8 | D43, B2 | from s3, seed 8 | 1634 | 38 | 238k (no gain) |
| run_d43_b3_s4 | D43, B3 | random, seed 4 | 1892 | 44 | 474k |
| run_d43_b4_s5 | D43, B4 | random, seed 5 | 2666 | 62 | 493k |
| run_d88_b1_s9 | D88 (n=704), B1 | random, seed 9 | 5456 | 124 | 193k |

Commands (examples): ./lift48 tabs/sg_86_2.tab 3,1,1,1,1,3,1,1,1,1,3,1,1,1,1,3 2 85 run_d43_b1_s1b run_d43_b1_s1.volt
./lift48 tabs/sg_88_5.tab 3,1,1,1,1,3,1,1,1,1,3,1,1,1,1,3 9 85 run_d88_b1_s9

## Best and verdict
- Best: run_d43_b1_s1b.edges, n = 688, bad = 1505 (score65; not a candidate). Not run through apsp (only score 0 needs it).
- Restarts from the best state (about 1.2M evaluations over three runs) never improved it, so it is a deep local minimum.
- Random-start runs end at 1500-2300 bad pairs. Each of the 8 sheets misses about 4-7 vertices at distance 6+.
- Larger group, same base: D88 (n = 704) gets much worse (5456), so the missing count grows with m.
- Verdict: the 4+4 base with m = 86 does not reach 0 under this annealing (floor about 1500 bad pairs). That does not rule out a
  zero from an exact search over the same family; the SA landscape is the limit here.
