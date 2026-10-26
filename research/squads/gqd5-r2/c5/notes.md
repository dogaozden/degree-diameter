# r2c5: typed HHHDHHD q=5 r=3 (rotational tournament), c freed points on every H->H arc

Layout (typed5.py): levels 0..6 with types HHHDHHD, arcs j->j+1,j+2,j+3 mod 7 (21 arcs). H->D arcs free the ovoid of
Q(4,5) (26, identity matching), D->H arcs free a partial spread of Q(4,5) = partial ovoid of W(5) of size 18 (c7/P18.json,
identity matching). Non-friendly arcs: the 10 H->H arcs (c freed points each, random matchings annealed) and the D->D arc
3->6 (cp freed lines, cp = 0 used). Hubs as build_typed: B-hubs take one out-slot per level, A-hubs one in-slot per level,
K_B = min over levels of out-slots, K_A = min over levels of in-slots; hub graph Y of max degree q-r = 2.
Counts: K_B = min(2c+26, 2*18+cp, 54), K_A = min(2c+18, 78, 52+cp), so n = 2184 + K_B + K_A.

## Results (apsp RESULT VALID d=9 D=5)
| c | cp | K_B | K_A | n | run |
|---|---|---|---|---|---|
| 2 | 0 | 30 | 22 | 2236 | c2a (30000 steps, T0 3) |
| 3 | 0 | 32 | 24 | 2240 | c3a (40000 steps) |
| 4 | 0 | 34 | 26 | 2244 | c4a (60000, ended at 2 bad), c4b (continue from c4a, T0 0.6) |
| 5 | 0 | 36 | 28 | 2248 | c5a (60000, ended at 8 bad), c5b (continue from c5a, T0 0.6) |

best.edges = c=5 graph (n = 2248, apsp VALID, degree min 6 max 9, bipartite). Pickled states: state_*.pkl (state dict).

## Moves that worked
- Energy = all ordered pairs at distance > 5 over the whole graph (hubs included), bit-parallel BFS from all vertices
  (wgr_eval.so, ~15 ms per evaluation).
- SA moves: swap two images in a non-friendly matching (85%), hub-slot swap in one level (B: sigma, A: tau), double edge
  swap in Y. Starting from random matchings, T0 = 3 linear cooling to 0.02 over the run; a second run from the saved state
  at T0 = 0.6 closes the last 2 to 8 bad pairs in every case.
- Random hub-slot assignments and random Y were enough; no structured choices were needed up to c = 5.

## Notes
- build_typed.py at c = 2 with the same P18 set (LD=1, local dualities) does not find a hub graph: best hub search 7 to 13
  bad pairs over 6 seeds x 40000 iterations. The SA above gets c = 2 valid (n = 2236) from random matchings, so the
  hub graph was not the binding constraint; the matchings were.
- Each extra unit of c adds 4 vertices (2 to K_B, 2 to K_A). cp > 0 is needed once 2c+26 > 36 + cp, i.e. c >= 6 (cp >= 2).
- Next: c = 6 with cp = 2 (same SA, then continuation at T0 0.6); K_B = 38, K_A = 30 would give n = 2252.
- Commands: python3 anneal5.py c cp steps seed T0 TAG [state.pkl]; apsp check: ../../../theorems/d5gq/apsp best.edges 9 5.
