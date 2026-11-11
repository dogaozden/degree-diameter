# c3: luck curve of Frobenius groups Z_p x| Z_k (N = p*k in 2,200..2,800)

Question: exact minimum cost of a Haar graph H(G,S), |S| = 4, diameter <= 9, for every Frobenius group
Z_p x| Z_k (k | p-1, k >= 8, r of order k mod p) with 2,200 <= p*k <= 2,800. Cost 0 gives 2N vertices.

Method
- list.py: enumerates the groups (22 of them; one isomorphism class per (p,k), since the order-k subgroup
  of Z_p^* is unique). groups.txt holds "N p k r".
- mkmeta.py (copy of tools/mkmeta.py) writes the table and Aut generators. Aut(Z_p x| Z_k) has order p(p-1);
  the generators (units times a, shifts by c) give all of it, so hx is exhaustive with the full reduction.
- hx (copy of tools/hx) with LIMIT 0, 1, 2, 4, 6, 8, 10 in turn; each level split into x-representative chunks.
  The first level that prints MIN c gives the exact minimum c; hits = raw hx count of sets with cost c.
- drive.py: resumable driver (state in res.jsonl, results in final.jsonl). Each call runs under ~70 s.
  Run again with `python3 drive.py 70` until it prints ALL DONE. Chunks that hit the shell timeout (machine
  load ~8 on 4 cores) are not counted; they are re-run as single representatives (CH = 1).
- Checks: cost-0 hits for 67/33/4, 151/15/2 and 71/35/2 verified with tools/apsp (RESULT VALID, D = 9, n = 2N).
  The cost of the first minimal hit for 101/25/5, 127/18/24, 97/24/4, 137/17/16, 127/21/25 was recomputed in
  numpy (indep_check.py) and agrees with hx.
- Scoreboard lines (card c3) use n = 2N (Haar graph vertices).

Table (hits = distinct sets {x,y,z} at the minimum; raw hx count in brackets when different)

| N    | p   | k  | r   | minimum | hits at minimum |
|------|-----|----|-----|---------|-----------------|
| 2211 | 67  | 33 | 4   | 0       | 552 (apsp VALID, n = 4422) |
| 2248 | 281 | 8  | 60  | >10     | - |
| 2265 | 151 | 15 | 2   | 0       | 24 (apsp VALID, n = 4530) |
| 2286 | 127 | 18 | 24  | 8       | 24 |
| 2316 | 193 | 12 | 49  | >10     | - |
| 2328 | 97  | 24 | 4   | 10      | 24 |
| 2329 | 137 | 17 | 16  | 2       | 336 |
| 2410 | 241 | 10 | 36  | >10     | - |
| 2439 | 271 | 9  | 106 | >10     | - |
| 2485 | 71  | 35 | 2   | 0       | 24 (apsp VALID, n = 4970; record group, r = 2 gives the same subgroup as 49) |
| 2504 | 313 | 8  | 5   | >10     | - |
| 2510 | 251 | 10 | 32  | >10     | - |
| 2525 | 101 | 25 | 5   | 2       | 48 |
| 2628 | 73  | 36 | 6   | >10     | - |
| 2667 | 127 | 21 | 25  | 10      | 24 |
| 2696 | 337 | 8  | 85  | >10     | - |
| 2710 | 271 | 10 | 27  | >10     | - |
| 2715 | 181 | 15 | 5   | >10     | - |
| 2748 | 229 | 12 | 18  | >10     | - |
| 2756 | 53  | 52 | 2   | >10     | - |
| 2758 | 197 | 14 | 6   | >10     | - |
| 2763 | 307 | 9  | 46  | >10     | - |

Counts: minimum 0 for 3 groups, 2 for 2, 8 for 1, 10 for 2, > 10 for 14 (exhaustive at LIMIT 10).

Rerun: `cd research/squads/deep-49/r1/c3 && python3 list.py | grep -v count > groups.txt && python3 drive.py 70`
(repeat until "ALL DONE"). Per-chunk log: res.jsonl. Final rows: final.jsonl. Hit sets: g/*.hits (cost c, x, y, z).
