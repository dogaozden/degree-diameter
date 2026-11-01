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

## Results (exact minima for the bi-coset family per (G,H) class unless marked 'sampled')
Cost C = far(A0)+far(B0); far pairs = M*C/2. Every edge list below was checked with apsp (diameter 10 when C>0).
| group | H | n | best C | status | file |
|---|---|---|---|---|---|
| S7 | involution, class K2 (of 3) | 5040 | **15** | EXACT (all {2,2},{2,1,1}; {1,1,1,1} disconnected) | runs/S7_h2_K2_full.edges (verified far 18900) |
| S7 | involution K1 | 5040 | 86 | exact {2,2} for K1 sampled 300k of 778k | runs/S7_h2_K1.edges |
| S7 | transposition K0 | 5040 | 140 | sampled | runs/S7_h2_K0.edges |
| A7x2 | central involution (Haar graph of A7) | 5040 | 6 | sampled 300k of huge {1,1,1,1} (= w1's Haar value) | runs/A7x2_h2_K2.edges |
| A7x2 | non-central involutions K1 / K0 | 5040 | 50 / 64 | sampled 300k of ~778k {2,2} | runs/A7x2_h2_K1.edges, K0 |
| M11 | order 3 (1 class) | 5280 | 38 | EXACT | runs/M11_h3_K0.edges |
| PSL(2,25) | order 3 (1 class) | 5200 | 30 | EXACT (= w7) | runs/PSL2_5^2_h3_K0.edges |
| PGL(2,25) | order 6, class K2 (of 3) | 5200 | 30 | EXACT (K0 10368, K1 424) | runs/PGL2_5^2_h6_K2.edges |
| PSigmaL(2,25) | order 6 (7 classes) | 5200 | 382 | EXACT (best class K2, K4) | in results.tsv |
| PSL(2,29) | V4 (1 class) | 6090 | 124 | EXACT | in results.tsv |
| PSL(2,27) | order 3 | 6552 | 176 | EXACT (= w7) | in results.tsv |
| A8 | order 8 (12 classes) | 5040 | 168 | EXACT for best class K0 (234 evals); others 598..10000 | in results.tsv |
| PSL(2,41) | A4 (2 classes) | 5740 | 530 | EXACT | in results.tsv |
| PSL(2,31) | C5 | 5952 | 11880 | disconnected (only fixed cosets) | in results.tsv |
| PSL(2,37) | C9 | 5624 | 11232 | disconnected (no orbits of size 3) | in results.tsv |

## Notes on the card
- PSL(2,31) with C5 and PSL(2,37) with C9, and PSL(2,32) with C11 (not run; same situation): every orbit of H on
  cosets has size 1 or is too large, so L lies in N(H) and the graph is disconnected.
- Subgroup classes are found by random sampling (normaliser chains). Classes can be missed; the counts per group
  come from the sampler, not from a full classification.
