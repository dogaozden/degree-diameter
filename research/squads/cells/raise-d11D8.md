# raise-d11D8: beat 2,258,520 at (Δ, D) = (11, 8)

Job "raise-11-8" (Haiku worker, cloud session, started 2026-10-25 ~07:55 UTC; budget 6 h, until ~14:00 UTC).
Record to beat: 2,258,520 = 2·|PSL(2,59) × Z_11| (N = 1,129,260), file `research/frontier/sols/d11D8_psl_59_11_orb5_ORBW5_s3.txt`,
k = 5 orbit method (`research/structured/`, STRUCTURE.md §8). Table value 2,246,940.

## Method
- Orbit annealing, `research/structured/haar_sym`, `ORBIT="5 2 1" ORBW=5 K=8 THREADS=1`: S = {e} ∪ two α-orbits of size 5,
  α = conjugation by an order-5 element × (z ↦ r z on Z_n). Only groups with every prime of n ≡ 1 mod 5 (so Fix(α) = C_Q(g) × 0).
- Candidate groups: `research/structured/tools/orb_screen.py 11 8 1129260 1200000 "5 2 1" --samples 400 --nmax 2000`
  (random symmetric S statistics: fix, min, p1, p10, median). Output in scratchpad (screen_k5.txt).
- Any N > 1,129,260 with a VALID check is a new record (2N > 2,258,520).

## Log
- 07:59 UTC: screen running. Baseline psl 59×11 random sample: fix 29, min 19, p1 28, p10 53.
  Started psl 19 × Z331 (N = 1,132,020, μ = 61.8, fix 9), ORBW=5, 2 seeds, 7200 s each.
- 08:03 UTC: screen done (60 candidates, `orb_screen.py ... --samples 400`; ranking by (p1+p10)/2 of random symmetric S cost).
  Baseline psl 59×11: min 19, p1 28, p10 53. Best near-record alternatives: psl 19×Z331 (N 1,132,020, fix 9: min 37, p1 47),
  sl 16×Z281 (N 1,146,480, fix 14: min 52, p1 71; SL(2,16) has no cyclic subgroup of order ≥ 64, so no wide rows).
  Everything with a cyclic factor of order ≥ 340 or with fix in the thousands is out (min ≥ 70–1,000,000).
  Running (ORBIT="5 2 1" ORBW=5 K=8 THREADS=1, 7200 s each): psl 19×Z331 seeds 1,2; sl 16×Z281 seeds 1,2.
- 08:25 UTC: at 08:23 psl 19×Z331 seed 1 best 6 (263k evals), seed 2 best 15; sl 16×Z281 stuck at 21–25 (194k evals).
  Stopped the sl 16×Z281 runs; started psl 19×Z331 seeds 3 and 4 (7200 s each).
- 10:01 UTC: psl 19×Z331 seeds 1, 2 (7200 s) ended unsolved: best 6 (≈1.35M evals each; cost = raw uncovered count,
  so one free orbit + one fixed element left). Seeds 3, 4 still running (best 10). Started seeds 5, 6 with RESTART=1, 10800 s.
- 10:26 UTC: psl 19×Z331 seeds 3, 4 (7200 s) ended unsolved, best 10 (≈1.35M evals). Seeds 5–8 (RESTART=1, 10800 s) running; 5, 6 at best 15 after 280k.
- 12:11 UTC: RESTART seeds 5, 8 reached best 5 (one free orbit uncovered); seeds 6, 7 best 10. No solution yet
  (~1.2–1.5M evals per run). Seeds 5, 6 end ~13:00, seeds 7, 8 ~13:25.

## Result (13:30 UTC): not beaten

All runs ended without a solution. No VALID graph above 2,258,520 was found, and nothing was saved to `research/frontier/sols/`.

| group | N | μ | fix | runs (seed, budget) | best cost (raw uncovered) | evals each |
|---|---|---|---|---|---|---|
| psl 19 × Z331 | 1,132,020 | 61.8 | 9 | 1, 2 (2 h); 3, 4 (2 h); 5, 6, 7, 8 (3 h, RESTART=1) | 6, 6, 10, 10, 5, 10, 10, 5 | 1.3–2.0 M |
| sl 16 × Z281 | 1,146,480 | 70.9 | 14 | 1, 2 (stopped at 1.9·10⁵ evals) | 21, 25 | 0.19 M |

- Best cost 5 (one free α-orbit uncovered, no fixed element) was reached twice (seeds 5 and 8, RESTART=1). Neither ever reached 0.
- For comparison, the record cell's seed 3 went down to 6 and then to 0 within about 6·10³ evaluations after about 1.2 M. Our psl 19 × Z331 runs did not complete that last step in ~1.4–2 M evaluations per seed.
- Screen (`orb_screen.py 11 8 1129260 1200000 "5 2 1" --samples 400`): the record group has the best random-sample statistics (min 19, p1 28). Every other group above 1,129,260 is at min ≥ 37. Cyclic factors ≥ 340, and groups with fix in the hundreds or thousands, are far worse.
- The μ_eff estimate (μ/5 + |Fix|·e^(−λ/5)) ranks psl 19 × Z331 below the record, but its annealing is harder. The random-sample statistics track annealing difficulty better than μ_eff does here.

## Assessment

These methods have not moved this cell with the groups tried. The next candidates would be: (a) more seeds on psl 19 × Z331 (an orbit space of about 10⁶ S per group, so the remaining uncertainty is mainly seed luck); (b) other k=5 conjugacy/r families for the same group (AR=, ALPHA= overrides in haar_sym); (c) psl 11 × Z1721 (N = 1,135,860, |Fix| = 4, random min 76). Each needs several hours of 4-core time. The budget for this job ended at about 14:00 UTC, so this session stops here.

Run logs: `research/structured/runs/raise11_8/`. Binary built from `research/structured/haar_sym.c` (`gcc -O3 -march=native -fopenmp`).
