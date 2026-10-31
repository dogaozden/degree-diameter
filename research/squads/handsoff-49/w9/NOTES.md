# w9 NOTES: bi-coset graphs of simple/perfect groups with larger stabilizers (follows w7)

Start: 2026-10-31 23:06 UTC. Deadline: about 01:05 UTC (2 hours). Last update: 23:06 UTC (setup).

## Plan
- Reduction used: S = HSH is a union of left cosets Hs; only the 4 cosets L = {cid(s)} matter, and L must be a union of
  right-H orbits on the cosets. Table T[c][i] = cid(rep_c * rep_i) (M x M), so each evaluation is 2 BFS on 2M vertices.
  Exhaustive search over all such L gives the exact minimum for each (G, H) class.
- Code: grp9.py (groups, subgroup classes up to conjugacy, table export), bi9.c (exhaustive/random search over L).
- Calibration target: PSL(2,25), H order 3 must reproduce w7's exact minimum C = 30 at n = 5200.

## Tool status (23:20 UTC)
- bi9.c + grp9.py work. Calibration: PSL(2,25), H order 3 -> exact minimum 30 at n = 5200 (same as w7), apsp diameter 10.
  Edge list runs/PSL2_5^2_h3_K0.edges (apsp VALID at 10, INVALID at 9).
- Exhaustive over S is cheap: M ~ 2500-3000 cosets, 10^4..10^6 evaluations per (G,H) class, about 50 us each.
  Subgroup classes of order h are found by random normalising chains and deduplicated by conjugacy canonical form.
- Connectivity note: if every orbit of right-H action on cosets of size <= 4 lies in N(H), the graph is disconnected
  (e.g. PSL(2,31) with C_5, PSL(2,32) with C_11): these cases are skipped by the search (no valid L with diameter).

## Results (exact minima for the bi-coset family, per (G,H) class)
| group | H | n | exact min cost | comp | file |
|---|---|---|---|---|---|
| PSL(2,25) | order 3 (1 class) | 5200 | 30 | {3,1} | runs/PSL2_5^2_h3_K0.edges (verified apsp diam 10) |
| M11 | order 3 (1 class) | 5280 | 38 | {3,1} ({1,1,1,1}: 10512) | runs/M11_h3_K0.edges (apsp diam 10, far = M*C/2 = 50160) |
