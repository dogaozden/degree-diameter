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
| sl 11 × Z91 / pgl 11 × Z91 | 120,120 | 40.3 | earlier: best 4 after 6e6 (sl) |
| prod sl 7 × psl 9 | 120,960 | 43.0 | earlier: best 8 after 1.4e6 |
| prod sl 3 × sl 9 × Z7, prod psl 7 × sl 9 | 120,960 | 43.0 | sweep 1 |
| sl 8 × Z241 | 121,464 | 44.6 | sweep 1 (first 3 s: best 27) |
| sl 7 × Z361 / pgl 7 × Z361 | 121,296 | 44.0 | sweep 1 |
| psl 9 × Z337 | 121,320 | 44.1 | sweep 1 |
| sl 9 × Z169 | 121,680 | 45.3 | sweep 1 |
| prod psl 3 × psl 5 × Z169 | 121,680 | 45.3 | sweep 1 |
| psl 17 × Z49 (record group, calibration) | 119,952 | 39.8 | sweep 1 (seeds 1, 2) |

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
- sweep 2 (`runs/raise8/jobs2.txt`, 1200 s per run): sl 11 × Z91 (two seeds, one with ORBW=3), pgl 11 × Z91, prod psl 7 × sl 9 × Z1.
