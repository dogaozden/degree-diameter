# h3 notes (type "1,1,3|1,1,3", n = 14m/3; groups of order 147 and 150)
Start 02:38 UTC, stop by 03:48 UTC. Single-threaded, all commands under 110 s.
## 02:36-02:52 work so far
- GAP tables: groups/sg_147_1..6 (6 groups of order 147), groups/sg_150_1..13 (13 groups of order 150).
- mcos screen (screen.sh, SECS=1, RANDCOMB=2, one seed, N = a,5-a,1,5-a,a,1,1,1,0), mcos cost (unweighted):
  147: g1 a3 26, a4 30, a5 80; g2 a3 68, a4 126, a5 120; g3 a3 28, a4 34, a5 70; g4 a3 32, a4 30, a5 66;
       g5 a3 32, a4 42, a5 72; g6 a3 94, a4 124, a5 150.
  150: g5 a3 33, a4 38, a5 83; g7 a3 36; g8 a4 82; g11 a5 80; g6 a3 52, a4 52; others 70-441 (see screen/screen_150.txt).
- score65 of the mcos screen graphs (edges/g*.edges): best bad 1617 (147_1 a3 and 147_3 a3), 1764 (147_1 a4, 147_5 a3), 1975 (150_5 a3).
- tabu3.c: full-neighbourhood tabu for the 9-block type. Objective = exact bad objective: cost = sum_o |O_o| * (vertices
  not within 5 of rep_o) = 2*bad (checked: cost 2058 gives score65 bad=1029). Env UNW=1 switches to the mcos-style cost.
  Speed about 45 ms per step (about 1000 steps per 45 s).
- tabu tenure test (147_1 a3, 24 s): T=2 2352, T=4 2058, T=10 2352 (cost = 2*bad).
- weighted tabu screen (tscreen.sh, 12 s, seed 11), cost=2*bad: a=3: g1 2352, g3 2450, g4 2646, g5 2352, g6 5096.
  a=4: g1 2646, g3 1666 (bad 833), g4 2352, g5 2940, g6 10388. a=5 is bad everywhere (3000+ bad).
## 02:52-03:11 tabu results (weighted objective, cost = 2*bad; bad = score65 bad)
- 147_3 a=4 is the only family point with bad below 800: seed 51, tenure 4, stall 600 (perturbation after 600 non-improving
  steps), 40 s: cost 588, score65 bad = 294 (file best_147_3_a4_bad294.edges, params best_147_3_a4_bad294.edges.par).
  The same settings with other seeds gave 588-1862 cost (bad 294-931); stall 40/300/1500 were worse on average.
- ILS from the bad=294 state (INIT=.par, stall 150 or 600, 40-45 s): no improvement.
- Best bad per group (tabu, 12-45 s runs, a = 3/4/5):
  147_3 a4 294; 147_5 a3 882; 147_1 a3 882; 147_5 a4 1029; 147_4 a4 1176; 147_4 a3 1323; 147_1 a4 1323;
  147_3 a3 1225; 147_6 a3 2548; 147_2 a3 3136, a4 4606; 150_7 a3/a4 1300; 150_5 a4 1975, a3 2100 (12 s runs only).
  a = 5 is far worse everywhere (bad 2900-7000). 150 groups were only screened (12 s); none beat 1300.
- Graphs checked with score65 only (no bad = 0 found, so apsp was not run).
- Distance-profile comparison (profile.py) of the bad=294 graph against shared/cost2_294_11.edges: different vertex-profile
  multisets, so the two are not isomorphic (same bad count only).
