# beyond-d13b round 2 (2026-11-02 00:01 UTC): 16 cards, one single-thread run each (autogroup nice 15), 75-minute boxes

Common rules: ../CARDS_COMMON.md (now forbidding every mcp__ tool). Director meanwhile: haarcheck_gen of (9,13)
SL(2,677) x Z13, then of (10,13) SL(2,601) x Z67.

| card | cell | direction |
|---|---|---|
| g01 | (5,13) | Frobenius k 53-61 above N 1.854M: continue Z35617 x| Z53 (cost 2) with new seeds, then Z31477 x| Z61 |
| g02 | (5,13) | Frobenius k 37-47 above 1.854M: fresh 300 s, then continuation chains |
| g03 | (5,13) | composite odd k (39, 45, 51, 57, 63, 33) above 1.854M |
| g04 | (5,13) | products F1 x F2 with F1 = Z7 x| Z3, Z13 x| Z3, Z31 x| Z5, Z29 x| Z7 |
| g05 | (6,13) | SL x Z_n, odd n 39-57 (sl 73 57, 79 45, 83 39), "3 2 0" + continuations |
| g06 | (6,13) | PSL x odd n 31-63 (psl 101 43, 89 63, 97 49, 113 31) |
| g07 | (6,13) | k = 5 orbits ("5 1 1"): sl 281 1 (vs "3 2 0"), sl 41 331, sl 61 101 |
| g08 | (6..8,13) | analysis: which elements are the holes of the constant-cost plateaus (UNCPRINT), NOTE.md |
| g09 | (7,13) | continue SL(2,163) x Z37 (cost 2, 320.5M) with new seeds and low TMAX; then sl 157 43, 181 27 |
| g10 | (7,13) | SL x Z_n, n 45-79 (sl 149 49, 137 63, 127 79, 139 61, 131 73) |
| g11 | (7,13) | k = 5 orbits ("5 1 2"): sl 131 71, psl 101 311, psl 199 41, psl 139 121, sl 139 61 |
| g12 | (8,13) | SL(2,359) x Z19 (mu 9.3), SL(2,347) x Z21; low-T continuation of SL(2,409) x Z13 |
| g13 | (8,13) | SL x Z_n, n 21-45 (sl 269 45, 293 35, 283 39) |
| g14 | (5,13) | wildcard (composite m, different r, hmeta knobs on the 35617 53 near miss, scans) |
| g15 | (6,7,13) | wildcard (other orbit shapes, alpha with more fixed points, knobs) |
| g16 | (8,13) | PSL x odd n (psl 283 77, 313 57, 281 79, 307 61) |
