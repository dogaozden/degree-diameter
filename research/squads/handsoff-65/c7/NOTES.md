# c7 notes (surgery and local search on whole graphs)

Files (all in c7/):
- h684.edges: the 684 Haar graph C6 x (C19:C3) = SmallGroup(342,12), rebuilt with `mcos` TYPE "1|1" (check.sh: bad 0).
- sa.c / sa: simulated annealing over 2-switches (edge B-endpoint swaps, degrees and bipartiteness kept), cost = far pairs.
  env: INFILE, RANDN (random 6-regular bipartite), GROW (add vertex pairs by 5-edge insertion), T0, T1, ITERS, SECS, SEED, OUT.
- ft.c / ft: focused tabu (guided 2-switches toward a far pair). gsa.c / gsa: guided SA (one guided proposal per step,
  Metropolis). lns.c: vertex-pair relocation LNS. symsa.c / symsa: Z_K-symmetric SA (orbit-wise 2-switches, K | n/2).
- damage.c: per-edge deletion damage + damage-guided insertion. tab2.c: tabu over 2-switches touching far vertices.
- scan2.c / scan3.c: EXHAUSTIVE scan of all valid 2-switches of an input graph (about 2.05M, ~5 min at n=686).
- analyze.py: far pairs by vertex, pairs involving the new vertices.

Commands used:
  INFILE=h684.edges GROW=1 SEED=15 T0=1.0 T1=0.3 SECS=500 OUT=... ./gsa      (guided SA from a 686 insertion)
  INFILE=best686_bad178.edges SECS=430 DTH=12 NEARFILE=near686.txt ./scan3   (exhaustive 2-switch scan)

Results:
- 684 Haar graph rebuilt: bad 0.
- Calibration (random 6-regular bipartite, plain 2-switch SA): n=300 solved in 7 s, n=400 in 27 s, n=500 stalls at 142.
  Focused tabu: n=300 solved in 23 steps, n=400 best 2 (120 s), n=500 best 376. Z7-symmetric SA: n=406 solved in 0.5 s,
  n=490 best 70 (K=7), 60 (K=6), 72 (K=3), 98 (K=2) in ~50 s each. Generic local search plateaus near 450-500.
- 686 = 684 + one vertex pair (5 edges moved, 11 added):
  * random single insertion: cost 283-303; best of 150 random insertions 214; damage-guided insertion (5 edges of least
    deletion damage) 186 (pool 80), 200-206 (larger pools). Deletion damage of one edge in the 684 graph: 44, 47, 49, 60, 81, 83
    (6 edge orbits under the group).
  * plain SA from 684+2: 258-268. Guided SA: 286 -> 178 (1.2M steps; the same basin, 177 from another seed, 214 start).
  * BEST: bad=178 (file best686_bad178.edges, verified by check.sh). Far pairs: 178 total; 38 involve the new vertices
    (685: 22, 684: 16); 140 are between old vertices. 223 vertices lie on a far pair.
  * EXHAUSTIVE scan of all 2.05M valid 2-switches of the 178 graph: none below 178. Smallest increase is +6 (13 switches
    with increase <= 12). So the 178 graph is a strict 2-switch local minimum.
  * Tabu over 2-switches (best of 1500 sampled switches touching far vertices, best admissible move): every step adds
    about +30..+60, the walk drifts up (cur 3339 after 2000 steps). No improvement.
  * Vertex-pair relocation LNS (contract a pair, re-insert best of 40 insertions): every move costs about +330. Useless.
- Symmetry: 686 with Z_7 symmetry from random start: best 3066 (plain schedule), so symmetric random starts do not reach n=686.

Verdict so far: single 2-switch moves are far too destructive at n=686 (every move about +40 or more, except +6 from the
178 graph). No record. Next (if time): more diverse insertions (choose the 5 edges from different damage orbits and spread
apart) with guided SA; a 688 version (Z_2-symmetric orbit insertion from 684) has not been tried.

Later runs (17:00-17:26):
- Uniform 2-switch SA from the 178 graph, T 3 -> 0.5, 2.4M moves: stays at 178 (cur 179).
- Guided SA from the damage-guided insertion (186): 181. From insertion seed 75 (219): 189. Basins at 177-189 for 686.
- Scoreboard: one line (686, bad=178, best686_bad178.edges). No line for the later runs (not better).
- Coordinator ideas: (1) damage-guided insertion done (186, no gain); (3) exhaustive 2-switch scan: 178 is a 2-opt local
  minimum; tabu over 2-switches drifts uphill (no gain). (2) covering of new vertices not tried as a separate search
  (far pairs involving the new vertices: 38 of 178).
- NEW BEST 686: bad=177 (c7/best686_bad177.edges, from guided SA seed 15 start 214; verified check.sh). Scoreboard updated.
  Final guided SA from it at T 0.5 -> 0.2 (1.7M steps): stays at 177. Final state: 686 vertices, 177 far pairs, no record.
