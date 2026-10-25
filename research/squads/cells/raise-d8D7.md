# Cell (Δ, D) = (8, 7): raise our record above 43,344

Job "raise-8-7" (Haiku worker, 2026-10-25). Record to beat: **43,344** vertices = 2·|SL(2,8) × Z_43| (N = 21,672),
Haar graph, k = 3 orbit search, ORBIT "3 2 2" (`../../structured/STRUCTURE.md` §4, file
`../../frontier/sols/d8D7_sl_8_43_orb3_s1.txt`). Table value 40,586.

## Why the window is narrow

A Haar graph on G has 2N vertices, N = |G|. The first-moment wall μ = N·exp(−W/N) with W = 137,257 for (8,7)
grows with N, so only groups with N in [21,673, ~22,100] have μ ≲ 43. Above that μ ≥ 45 and the orbit search has
not solved anything at (8,7) (pgl 9 × Z31, μ 47.6: best cost 9 after 8.7·10⁶ evaluations).

Candidates with N in [21,673, 22,500] from `../../structured/tools/orb_screen.py 8 7 21673 26000 "3 2 2" --anyn`
(random-S minimum cost over 300 samples; the record group has min 17 at μ 38.5):

| group | N | 2N | μ | fix | random min |
|---|---|---|---|---|---|
| pgl 5 × Z181 | 21,720 | 43,440 | 39.1 | 5 | 84 |
| sl 5 × Z181 | 21,720 | 43,440 | 39.1 | 5 | 180 |
| prod psl 3 × psl 3 × Z151 | 21,744 | 43,488 | 39.4 | 8 | 1036 |
| sl 7 × Z65, pgl 7 × Z65 | 21,840 | 43,680 | 40.7 | 29 | 69–70 |
| psl 9 × Z61 | 21,960 | 43,920 | 42.4 | 8 | 59 |
| psl 17 × Z9 | 22,032 | 44,064 | 43.4 | 26 | 29 |
| pgl 4/sl 4/psl 5 × Z367 | 22,020 | 44,040 | 43.2 | 2 | 414+ (poor) |
| pgl 9 × Z31, sl 9 × Z31 | 22,320 | 44,640 | 47.6 | 8–17 | 36, 46 |

Other (k, m, f) values for d = 8: k = 2 (m = 4, f = 0 or m = 3, f = 2), k = 4 (m = 2, f = 0), k = 5 (m = 1, f = 3). These
screened worse on the same windows (random min ≥ 40 on the best ones).

## Runs

- Calibration (120 s, one thread, ORBIT "3 2 2", seed 1, ~6·10⁶ evals each): pgl 7×65 best 6, pgl 9×31 best 9, psl 17×9
  best 10, psl 9×61 best 12. None solved.
- Wave 1 (3600 s each, seed 11, logs in the scratchpad): psl 17×9, pgl 7×65, psl 9×61, pgl 5×181.

- Wave 1 result (3600 s each, seed 11, ~1.6–2.3·10⁸ evals each): psl 17×9 best 3, pgl 7×65 best 6, psl 9×61 best 12,
  pgl 5×181 best 24. None solved.
- Wave 2 (3600 s each): psl 17×9 with ORBW=3 (seed 12), psl 17×9 with RESTART=1 (seed 13), pgl 7×65 with ORBW=3
  (seed 12), psl 17×9 plain (seed 14).

- Wave 2 result (3600 s each): psl 17×9 best 3 in all three variants (ORBW=3 seed 12, RESTART=1 seed 13, plain seed 14),
  about 1.6·10⁸ evals each. pgl 7×65 with ORBW=3 best 9 (worse than plain's 6). None solved. The cost-3 floor on
  psl 17×9 is the same across seeds and variants, which suggests no orbit-symmetric solution for this α, not a slow search.
- Wave 3 (3600 s each): sl 7×65 (seed 21), pgl 9×31 (seed 21), sl 9×31 (seed 21), psl 9×61 with RESTART=1 (seed 22).

- Wave 3 result (3600 s each): pgl 9×31 best 6 (seed 21), sl 9×31 best 6 (seed 21), sl 7×65 best 6 (seed 21),
  psl 9×61 with RESTART=1 best 12 (seed 22). None solved. About 2.2·10⁸ evals each.

## Status: stopped, nothing above 43,344

Three waves (about 12 one-hour runs, roughly 2.5·10⁹ evaluations on 4 cores) over every candidate group with
N in [21,673, 22,500] and the k = 3, m = 2, f = 2 orbit structure. Best costs: 3 (psl 17×9, three variants and seeds),
6 (pgl 9×31, sl 9×31, sl 7×65, pgl 7×65 plain), 12 (psl 9×61), 24 (pgl 5×181). Nothing solved.

Why stopped: the cost floors are the same across seeds and variants, the group windows are exhausted, and BEYOND_RANDOM
§1.5 already puts (8,7) near the orbit-space ceiling. Not proven: each orbit space is still far larger than the
evaluations spent, so a much longer run on psl 17×9 (cost 3) or pgl 9×31 (cost 6) remains the cheapest next step.

Not tried: k = 2, 4, 5 structures on these groups beyond the random-S screen; Lean/lift routes.
