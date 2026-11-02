# c1 (deep-65b round 1): tabu ranking of groups for the [[1,5],[5,1]] split family

Start 23:08 UTC, finished about 23:50 UTC (60-minute box).

## Files
- c1.c: tabu search over (E1,E2), six-condition cost of tools/split15.c (sum of the six miss counts). Binary c1 (RESTART 1500).
  c1r300 = same with RESTART 300 (only used for one test).
- scan.sh: foreground driver; runs c1 on pending groups from todo.txt (or $TODO), appends raw.txt lines
  "order id seed best t_best name", stops starting groups after ~85 s per call.
- todo.txt: the 160 non-abelian groups of orders 172,174,176,178,180,182,184,186,188,190,196,198,200 (abelian skipped; 192 absent).
- todo2.txt, todo3.txt, todo4.txt, todo5.txt: candidate subsets for extra seeds. raw.txt: all runs. best_by_group.tsv, ranking.tsv.
- sg176_23_seed3.edges (n=704, 2112 edges): the cost-0 graph. sg176_23_split15.edges: same graph built by split15 edges (same undirected edge set).

## Commands (exact)
- gcc -O3 -march=native -Wall -o c1 c1.c -lm
- cross-check: for 12 random 10-element states on sg_176_17.tab, `./c1 TAB cost ...` equals `shared/split15 TAB cost ...` (12/12 agree).
- calibration: ./c1 groups/sg_176_17.tab 1 25 ; ./c1 groups/sg_176_17.tab 2 25 -> best 6 (seed 1), 2 at 3.05 s (seed 2).
  9 s runs (scan): seed1 8, seed2 2 (at 5.05 s), seed3 17, seed4 7, seed5 8.
  RESTART 300 on 176_17 at 9 s: seeds 1,2,3 -> 7, 2, 8 (no clear gain, kept RESTART 1500).
- screen: TODO=... ./scan.sh 9 SEED (seed 1 on all 160 groups; seeds 2,3 on best candidates; seeds 4,5 on top 5).
- cost-0 run: ./c1 groups/sg_176_23.tab 3 9 sg176_23_seed3.edges
  -> RES n=704 seed=3 best=0 t_best=5.75 E1=55,34,136,108,115 E2=37,122,162,26,46 brk=0,0,0,0,0,0
- check: shared/score65 sg176_23_seed3.edges -> SCORE n=704 edges=2112 maxdeg=6 bipartite=yes simple=yes bad=0 diam=5
          shared/apsp sg176_23_seed3.edges 6 5 -> RESULT VALID d=6 D=5 n=704
          shared/split15 groups/sg_176_23.tab edges 55 34 136 108 115 37 122 162 26 46 sg176_23_split15.edges -> same score; same undirected edges.

## Results
- Only cost 0 found: SmallGroup(176,23) = C11 x (C8 : C2), |Aut| 160, n = 704 > 684. Found on seed 3 at 5.75 s; seeds 1,2,4,5 (9 s each) gave 5,7,9,7.
- Best costs (min over seeds) in ranking.tsv: 176_23 0; 174_1 2 (C29 x S3); 176_17 2 (C11 : Q16, the calibration group, optimum 2 found
  once); 176_1 3 (C11 : C16); 176_15 3 (C11 : QD16); 176_39 4 (C22 x Q8); then several at 6 (176_24, 176_25, 176_26, 176_38, 176_40, 180_6, 180_13, 180_21).
- Noise: each 9 s run is essentially one tabu trajectory (about 500-650 iterations; ~65 iterations/s at m=176). Seeds vary a lot
  (e.g. 176_17: 8, 2, 17, 7, 8). Cost-7/8-level groups may hide zeros; the ranking is a weak screen, not a proof of absence.
- The card asked for 2 seeds of 20-30 s per group; this run used 9 s per seed (budget), one seed on all 160 groups.

## Notes
- Two shared files (tools/split15.c and shared/split15 source/bin) show mtime 23:42:34 in this session; I did not edit them.
  split15 still prints 0 0 0 0 0 0 for the cost-0 state and builds the same edge set, so the checks above are unaffected.
- No git commands, no background processes, no sleeps.
