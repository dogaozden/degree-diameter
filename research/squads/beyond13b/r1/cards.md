# beyond-d13b round 1 (2026-11-01 23:03 UTC): 16 cards, one single-thread nice-10 run each, 60-minute boxes

Common rules: ../CARDS_COMMON.md. Director meanwhile: haarcheck_gen of the (10,13) find SL(2,601) x Z67 (4 threads, 10 GB).

| card | cell | direction | first groups |
|---|---|---|---|
| f1 | (5,13) | single Frobenius Z_m x\| Z_k, k 37-47 (hmeta) | 48767 37, 41969 43, 38447 47, 44281 41 ... |
| f2 | (5,13) | single Frobenius, k 53-61 | 30013 61, 31153 59, 34981 53 ... |
| f3 | (5,13) | single Frobenius, k 13-31 | 62119 29, 94811 19, 78569 23 ... |
| f4 | (5,13) | products of two Frobenius groups (haar_gen3s) | (Z11 x\|_4 Z5) x (Z_m x\| Z_k) ... |
| f5 | (5,13) | wildcard (composite k, composite m, 3 factors, x Z_n) | card's choice |
| e1 | (6,13) | PSL/SL x Z_n, n 21-43, "3 2 0" | psl 103 39, psl 107 35, sl 101 21, sl 89 31 |
| e2 | (6,13) | SL(2,p), n = 1, "3 2 0" | sl 277 1 -> 281 1 -> 283 1 |
| e3 | (6,13) | Frobenius, random S (hmeta), long runs | 342821 61, 486331 43, 445091 47 ... |
| e4 | (6,13) | SL x Z_n, n 37-73 (the PSL(2,83) x Z73 shape in SL) | sl 83 37, 79 43, 71 61, 67 73 |
| e5 | (6,13) | wildcard (k = 5 orbits, RANDORB screen, knobs) | card's choice |
| d1 | (7,13) | SL x Z_n, n 1-13, "3 2 1" | sl 283 7 -> 263 9 -> 233 13 |
| d2 | (7,13) | SL x Z_n, n 21-37 | sl 197 21, 173 31, 163 37 -> 199 21 |
| d3 | (7,13) | PSL x Z_n, odd n 27-73 | psl 173 61, 163 73, 227 27 -> 197 43 |
| d4 | (7,13) | wildcard (other orbit structures, k = 5/7, screen, knobs) | card's choice |
| c1 | (8,13) | SL x Z_n, n 1-9, "3 2 2" | sl 461 9 -> 503 7 -> 967 1 -> 467 9 |
| c2 | (8,13) | SL x Z_n, n 13-43 | sl 409 13 -> 307 31 -> 277 43 |

(9,13) and (10,13) stay with the director (memory: 2 GB and 7.5 GB per run).
