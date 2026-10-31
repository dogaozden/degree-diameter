# w9 NOTES: bi-coset graphs of simple/perfect groups with larger stabilizers (follows w7)

Start: 2026-10-31 23:06 UTC. Deadline: about 01:05 UTC (2 hours). Last update: 23:06 UTC (setup).

## Plan
- Reduction used: S = HSH is a union of left cosets Hs; only the 4 cosets L = {cid(s)} matter, and L must be a union of
  right-H orbits on the cosets. Table T[c][i] = cid(rep_c * rep_i) (M x M), so each evaluation is 2 BFS on 2M vertices.
  Exhaustive search over all such L gives the exact minimum for each (G, H) class.
- Code: grp9.py (groups, subgroup classes up to conjugacy, table export), bi9.c (exhaustive/random search over L).
- Calibration target: PSL(2,25), H order 3 must reproduce w7's exact minimum C = 30 at n = 5200.
