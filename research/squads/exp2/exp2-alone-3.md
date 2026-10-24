# exp2-alone-3 report: bipartite (Δ, 7) cells

Worker: Haiku, working alone (no subagents). Focus cell (7,7). Start 2026-10-24 16:56 UTC; last search ended 19:48 UTC.
Wall time about 2 h 55 min (cap 4 h). Final budget_units 0.004 (cap 1.5), from `tools/session_usage.py`; the usage log is
`research/squads/usage/exp2-alone-3.jsonl`.

## Result

| cell | table (vertices) | best valid (vertices) | ratio | cells beaten |
|---|---|---|---|---|
| (7,7) | 23,436 | **19,152** (sl 8 × Z19, orbit-symmetric S) | 0.817 | 0 |
| (9,7) | 117,648 | none | – | 0 |
| (11,7) | 398,580 | none | – | 0 |

Three valid (7,7) graphs, each checked by `research/frontier/build_haar2.py` (ecc 7 from both sides, no unreached vertices,
7-regular, no duplicate edges):

| file (research/frontier/sols/) | group G | N = \|G\| | vertices | ratio | how found |
|---|---|---|---|---|---|
| `d7D7_orb_sl_8_19_s1.txt` | SL(2,8) × Z19 | 9,576 | 19,152 | 0.817 | orbit mode, ORBIT="3 2 1", solved in 0.1 s |
| `d7D7_sl_9_13_s3.txt` | SL(2,9) × Z13 | 9,360 | 18,720 | 0.799 | plain annealing, solved in 22 s on seed 3 |
| `d7D7_sl11_7_s1.txt` | SL(2,11) × Z7 | 9,240 | 18,480 | 0.788 | plain annealing, solved in 0.2 s |

No graph beats the table value, so no cell was beaten. Score-wise the only thing gained is the ratio for (7,7).

## What I did

1. **Plain annealing (haar_gen3)**, d = 7, D = 7 (odd: two covering conditions, one per side). Groups of order 9,000–12,000
   (SL/PSL/PGL(2,q) × Z_n). Solved at 9,240 (sl 11 × Z7), 9,360 (sl 9 × Z13). Near misses at cost 2 on sl 7 × Z28 (9,408),
   psl 11 × Z14 (9,240). Costs grew quickly above ~9,500: sl 9 × Z14 (10,080) 10, sl 8 × Z20 17, sl 7 × Z29 6, psl 13 × Z9
   (9,828) 7–8, sl 11 × Z8 (10,560) 14, sl 7 × Z31 (10,416) 18. Groups of order 11,880 and up were far off (costs 50–70).
2. **Orbit-symmetric S (haar_sym.c from branch claude/structured-search-orbit-w5dd4f, ORBIT="3 2 1")**: S = {e} plus two
   orbits of size 3 under an automorphism α = conjugation by an order-3 element × (z ↦ r z on Z_n). This is what gave the best
   result. It solved sl 8 × Z19 (9,576) immediately, but only where the multiplier r is non-trivial (a cube root of 1 mod n).
   With r = 1 (n = 20, 22) it stalled at costs 600–1,300, so the fixed-point penalty dominates.
   Orbit results above 9,576 (all failed, 540 s each, 1–4 seeds): sl 9 × Z14 10; sl 7 × Z31 6 (4 seeds); pgl 7 × Z31 6;
   psl 9 × Z27 48; psl 9 × Z31 33; sl 5 × Z91 50; sl 5 × Z97 98; sl 11 × Z9 54; psl 11 × Z18 89 (both 11,880);
   sl 4 × Z163 36; sl 4 × Z181 96; sl 3 × Z409 1,460; sl 3 × Z487 3,752; agl1 103 14,252.
3. **psl 13 × Z9 (9,828)** stalled at exactly one uncovered element in every run (9 seeds, weights ORBW = 1 and 5, multipliers
   r = 4, 7, and the f = 4, m = 1 split). This looks like a structural obstruction for that α, not bad luck. I did not diagnose it.
4. **Involution orbits (ORBIT="2 3 1")** were much worse: costs 45–173 at 9,828–11,880.

Full list of runs (75 entries, with the best cost reached, evals and time): `research/squads/exp2/exp2-alone-3-runs.txt`.

## What worked, and what did not

- Working: the annealing tool is fast on these groups (~40–60k evaluations/s), and the checker is independent of the search.
  The orbit method is the only thing that moved the frontier past ~9,400 for (7,7).
- The solves at 9,240 and 9,360 came in seconds or after a few runs, so the wall is heavy-tailed. The 9,576 orbit solve was
  also quick. Stalls at cost 1–6 were common and did not resolve with more seeds.
- Not working: groups of order ≥ 9,780 with plain or orbit search (except sl 8 × Z19, which is 9,576), any involution
  orbit, and any group with a trivial multiplier.
- Why I stopped: with about an hour left and no new hits in the last ~8 batches (psl 13 × Z9 stuck, sl 7 × Z31 stuck at 6),
  further seeds looked like a low-probability use of the remaining time. The size law in SIZE_LAW.md predicts a plain-random
  ceiling around 9,000–10,000 per side for this cell, and orbit mode is the only route found above it. Beating the table
  (N ≥ 11,719 per side) needs an algebraic construction; none was tried.

## Caveats

- Verification is only `build_haar2.py` (independent Python checker, all three files VALID). I did not run the APSP C checker.
- The table value 23,436 is interpreted as vertices (2N), matching the frontier TABLE.md convention.
- The (9,7) and (11,7) cells were not searched beyond the runs listed above (none reached a valid graph).
