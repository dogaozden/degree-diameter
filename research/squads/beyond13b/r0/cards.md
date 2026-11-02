# beyond-d13b round 0 (ABORTED after 4 minutes, 2026-11-01 22:56-23:00 UTC)

Launched with Agent isolation "remote", expecting one cloud container per card. The cards ran in the director's container instead, all in one work/ folder: tags and output files collided, ~40 threads ran on 4 cores, and the director's 29-billion check was OOM-killed. All 17 cards were stopped and their processes killed; no results were kept. The cards as written:


Every card starts with the common header:

> You are squad card r1/<ID> of job beyond-d13b, running in your own cloud container. Step 0: `cd /home/user/degree-diameter
> && git fetch -q origin claude/beyond-d13-extend-5n8uwl && git reset -q --hard FETCH_HEAD && cat
> research/squads/beyond13b/CARDS_COMMON.md`. Read it and follow it exactly. Time box: 45 minutes of searching from your
> first bg.sh, then kill leftovers and send the final reply.

Groups are written "fam p n" (G = SL(2,p) x Z_n or PSL(2,p) x Z_n); 2N = vertices; mu = size-law mu. "Ladder": go to
the next rung when a rung reaches cost 0.

| card | cell | direction | groups |
|---|---|---|---|
| a1 | (10,13) | SL x Z7 (big p, fewest central holes), ORBIT "3 3 1" | sl 1283 7 (2.957e10, mu 6.9); up: sl 1289 7 (2.998e10); fallback sl 1277 7 (2.915e10) |
| a2 | (10,13) | SL x Z19 / Z27 / Z13 | sl 919 19 (2.949e10, mu 6.5); up: sl 821 27 (2.988e10); fallback sl 1039 13 (2.916e10) |
| a3 | (10,13) | SL x Z37 / Z43 | sl 701 43 (2.962e10, mu 7.2); up: sl 739 37 (2.987e10); fallback sl 733 37 (2.914e10) |
| a4 | (10,13) | RANDORB screen of 9 shapes at ~2.9-3.0e10, then anneal the best | sl 1283 7, 1181 9, 1039 13, 919 19, 821 27, 751 35, 739 37, 701 43, 601 67 |
| b1 | (9,13) | SL small n, f = 0 ("3 3 0"), ladder in mu | sl 829 7 (mu 11.2) -> 677 13 (14.1) -> 599 19 (18.1) -> 601 19 (22.2) |
| b2 | (9,13) | SL with n = 1, 9, 35, 49, f = 0 | sl 433 49 (10.6) -> 487 35 (14.8) -> 1597 1 (17.2) -> 769 9 (19.0) |
| c1 | (8,13) | SL small n, "3 2 2", two seeds per rung | sl 461 9 (9.8) -> 503 7 (12.0) -> 967 1 (15.9) -> 467 9 (20.5) -> 509 7 (23.3) |
| c2 | (8,13) | SL mid n + one PSL comparison | sl 409 13 (11.6) -> 349 21 (12.4) -> 307 31 (13.6) -> 277 43 (19.4); psl 331 49 (11.4) |
| d1 | (7,13) | SL small n, "3 2 1", 4 single-thread runs, ladder to mu 30+ | sl 283 7, 541 1 (11) -> 263 9, 547 1, 233 13 (19-21) -> cands.py above 3.3e8 |
| d2 | (7,13) | SL n 21-37 + PSL comparison | sl 197 21, 173 31, 163 37 (13-14) -> 199 21 (23.1); psl 163 73 (10.5) |
| e1 | (6,13) | PSL/SL moderate n, "3 2 0" | psl 103 39 (12.8), psl 107 35 (14.1), sl 101 21 (16.2), sl 89 31 (18.8), psl 101 43 (23.0), sl 83 39 (25.4) |
| e2 | (6,13) | SL n = 1, "3 2 0" | sl 277 1 (12.4) -> 281 1 (23.6) -> 283 1 (32.2) |
| e3 | (6,13) | odd-order Frobenius Z_m x| Z_k, random S (hmeta), 4 runs | mpick.py 6 13 2.09e7 2.25e7 |
| f1 | (5,13) | single Frobenius Z_m x| Z_k (hmeta), 4 runs, ladder in N | mpick.py 5 13 1.80e6 1.95e6 |
| f2 | (5,13) | products of two Frobenius groups (haar_gen3s, SAVEBEST/START) | (Z11 x|_4 Z5) x (Z_m x| Z_k) etc., N 1.80-1.95e6 |
| f3 | (5,13) | wildcard: a family none of f1, f2 uses | card's choice |
| w1 | (6,13) or (7,13) | wildcard: an approach none of the other cards uses | card's choice |

Director (local): (10,13) sl 601 67 (2.909e10), ORBIT "3 3 1", THREADS 4.
