# Raise (8,8): notes for resuming

Job "raise-8-8" (2026-10-25, Haiku worker). Goal: beat our record 239,904 vertices at (Δ,D) = (8,8)
(table 201,480; Moore bound 1,921,600).

## Where the record stands

- 239,904 = 2·|PSL(2,17) × Z_49|, Haar graph, `sols/d8D8_psl_17_49_orb3_s1.txt`, α = conj by order-3 element × z→18z,
  ORBIT="3 2 2" (k = 3, m = 2 free orbits, f = 2 fixed generators incl. e), μ = 39.8, solved in 88k evaluations.
- Reference: research/structured/STRUCTURE.md §3–§4, §8.

## Key numbers

- μ is computed from the GROUP order |G| (half the vertex count): μ = |G| exp(−W/|G|), W = 960,800 for (8,8).
  d ln μ / d ln|G| ≈ 1 + W/|G| ≈ 9, so +1 % in |G| is about +9 % in μ.
- Every graph in the window |G| ∈ (119,952, 124,000] has μ between 40 and 52. Wall for k = 3 (STRUCTURE §3): μ ≈ 45–50.
- Speed: haar_sym on one thread ≈ 10⁴ evaluations/s at N ≈ 120k (60 s ≈ 6·10⁵ evals).

## Candidate orders (proper k = 3: all primes of n ≡ 1 mod 3), |G| just above 119,952

| group | |G| | μ | status |
|---|---|---|---|
| sl 11 × Z91 / pgl 11 × Z91 | 120,120 | 40.3 | best 3 (sl, 1.2e7 evals) |
| psl 11 × Z182 (anyn) | 120,120 | 40.3 | best 3 on 3 seeds, 1.2·10⁷ evals each (stalls at one orbit) |
| prod sl 7 × psl 9 | 120,960 | 43.0 | earlier: best 8 after 1.4e6 |
| prod sl 3 × sl 9 × Z7, prod psl 7 × sl 9 | 120,960 | 43.0 | sweep 1 |
| sl 8 × Z241 | 121,464 | 44.6 | sweep 1 (first 3 s: best 27) |
| sl 7 × Z361 / pgl 7 × Z361 | 121,296 | 44.0 | sweep 1 |
| psl 9 × Z337 | 121,320 | 44.1 | sweep 1 |
| sl 9 × Z169 | 121,680 | 45.3 | sweep 1 |
| prod psl 3 × psl 5 × Z169 | 121,680 | 45.3 | sweep 1 |
| psl 17 × Z49 (record group, calibration) | 119,952 | 39.8 | sweep 1 (seeds 1, 2) |

- sweep 3 result (`runs/raise8/jobs3.txt`, 1200 s, ~1.2·10⁷ evals each), no solution: psl 11 × Z182 best 3 on all three
  seeds (incl. ORBW=3); sl 11 × Z91 (fresh seed) best 4.
- sweep 4 (`runs/raise8/alpha_r81.sh`, 1200 s): the other order-3 multiplier (AR=81) on psl 11 × Z182 (two seeds), sl 11 × Z91
  and pgl 11 × Z91.

- sweep 5 (`runs/raise8/restart.sh`, RESTART=1, 1200 s): psl 11 × Z182 best 3 (two seeds), sl 11 × Z91 best 3,
  prod psl 7 × sl 9 × Z1 best 5. No solution.

Total: about 25 runs and roughly 2.5·10⁸ evaluations on 120,120 (the lowest order above the record), 120,960, 121,296–121,680.
Best cost 3 (one uncovered orbit), never 0. The record stays at 239,904.

## Why I stopped (final)

Raise not achieved. The nearest candidate is 240,240 (sl/pgl/psl 11 family, |G| = 120,120, cost 3), and it did not solve.

Groups inside the window (|G| > 119,952, μ ≈ 40–52): only a handful exist with k = 3 and all primes of n ≡ 1 mod 3.
Those at μ ≈ 40 (120,120) stall at cost 3–4 (one or two uncovered orbits) for 10⁷ evaluations per seed. Those at μ ≈ 43–45
with a large cyclic factor (Z337, Z361, Z241, Z169) stall at cost 20–70. The record group solves quickly on several seeds only
because its |G| sits exactly at the edge of the window. Pushing past it needs μ ≈ 45–50, which the k = 3 orbit wall in
STRUCTURE.md §3 puts at 10⁷ evaluations or more, with no structure I could find that does better. The only other routes
here (k = 5 with f = 3 and a single orbit, involutive α) were already ruled out in STRUCTURE.md §5 and §8.

## Tools

- `research/structured/tools/raise8_queue.sh JOBFILE OUTDIR SECS PAR`: job lines `SEED ORBW GROUP...`
  (ORBW 0 = default). Logs and any cost-0 graph go to OUTDIR (runs/raise8/).
- Verify every find with `research/frontier/build_haar2.py` (N = 2|G| ≤ 20M); save into research/frontier/sols/d8D8_*.

## Log

- sweep 1 (`runs/raise8/jobs1.txt`, 300 s per run, 4 at a time, ~3·10⁶ evals each), no solution:
  - sl 11 × Z91 (120,120, μ 40.3): best 4 (seed 2); pgl 11 × Z91: best 5. Closest to a record.
  - psl 17 × Z49 (the record group, calibration): best 3 on both seeds at 300 s. The record itself was a lucky
    88k-eval solve, so solve times are heavy-tailed.
  - prod psl 7 × sl 9 × Z1 (120,960, μ 43.0, fix 53): best 7. prod sl 3 × sl 9 × Z7 (fix 107): best 8.
  - sl 9 × Z169 (121,680, μ 45.3): best 22. sl 8 × Z241 (121,464, μ 44.6): best 21. psl 9 × Z337 (121,320): best 60–72.
    sl 7 × Z361 and pgl 7 × Z361 (121,296): best 48–66. prod psl 3 × psl 5 × Z169: best 37,477 (fix 719, rejected).
  - Reading: cost floors near 20–70 at μ ≈ 44–45 with a large cyclic factor; the small-|Fix| groups with small n do best.
- sweep 2 (`runs/raise8/jobs2.txt`, 1200 s per run, ~1.2·10⁷ evals each), no solution:
  - sl 11 × Z91 (120,120): best 3 (seed 3), 6 with ORBW=3 (seed 4). pgl 11 × Z91: best 4.
  - prod psl 7 × sl 9 × Z1 (120,960): best 6.
  - Calibration (psl 17 × Z49, the record group): solved again in 55 s and 204 s at 239,904. Not a raise.
- sweep 3 (`runs/raise8/jobs3.txt`, 1200 s): psl 11 × Z182 (anyn: n = 2·7·13, α = z→9z, |Fix| = 11, μ 40.35), seeds 3, 4
  and ORBW=3 seed 5; sl 11 × Z91 fresh seed 6.
