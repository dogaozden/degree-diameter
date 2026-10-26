# Raise the (Δ,D) = (12,9) record, round 3 (Haar graphs)

Job "raise3-12-9", Haiku worker, branch `claude/raise-d12d9-bipartite-round3-fhhyi9`.
Round 2 is on `claude/raise-d12d9-bipartite-record-b26a5o` (notes `research/squads/cells/raise-d12D9-round2.md`
there). Round 1 is on `claude/raise-d12d9-bipartite-record-f510kc`.

## RECORD (round 3, first success)

**35,445,648 vertices** = 2 · |SL(2,83) × Z31|, N = 17,722,824, k = 3, m = 4, f = 0, ORBW = 3, seed 3, 184k evals (6,983 s).
File: `research/frontier/sols/d12D9_sl_83_31_orb3f0_orbw3_s3.txt`. Checks: `haarcheck_sl` VALID and `haarcheck2` VALID,
both d = 12, D = 9, all 17,722,824 per side reached, ecc 9 (outputs in `research/frontier/runs/cloudcheck/`).
Log: `research/structured/runs/d12D9r3_sl83_31_orbw3_s3.log`.

**New bar: N > 17,722,824** (2N > 35,445,648).

## Bar to beat (at the start of round 3)

- Master (README, RESULTS) still says 34,026,720 (sl 41 × Z247, N = 17,013,360).
- Round 2's branch has VERIFIED finds above that, not yet recorded by the coordinator:
  **35,393,904** = 2 · |PSL(2,73) × Z91| (`research/frontier/sols/d12D9_psl_73_91_orb3f0_orbw3_s5.txt`).
  Re-checked in this round with `research/structured/tools/haarcheck_psl` (VALID, 20 s).
- So the bar used here is **N > 17,696,952** (2N > 35,393,904). Anything between 34,026,720 and 35,393,904 is already
  beaten by round 2 and would not be a new record.

## Round 2 (what is NOT repeated here)

- Success: psl 73×Z91 ORBW=3 seed 5 (111k evals); sl 47×Z169 ORBW=3 seed 6 (18.5k evals).
- Tried and unsolved above the bar, best cost: sl 83×Z31 (seed 1 best 8, seed 2 best 6 at 152k evals),
  sl 43×Z223 (seed 1 best 12 at 157k, seed 2 stuck at 24), psl 47×Z343 (seed 1 best 6 at 176k, seed 2 best 18).
- Not done in round 2: a PGL / GF(q) checker, a search change (targeted moves on the uncovered set), k ≠ 3.

## Plan for this round

1. Candidate groups with N in (17,696,952, ~17.9M] that have an independent checker (prime q, SL or PSL) and
   n whose prime factors are ≡ 1 mod 3 (so α acts on Z_n): sl 43×Z223, sl 83×Z31, psl 47×Z343 (round-2 leads),
   then new ones from the screen: sl 41×Z259 (N 17,839,920, μ 32.4), psl 61×Z157 (17,813,220, μ 31.8),
   sl 61×Z79 (17,926,680, μ 34.8), psl 53×Z241 (17,933,292, μ 34.9).
2. Structure: k = 3, m = 4, f = 0 (ORBIT="3 4 0"), ORBW=3, THREADS=1, K=8, 2 h per run, 4 runs in parallel.
3. Check k = 4 (ORBIT="4 3 0") on groups where the random-S screen says it is competitive; sl 41×Z257
   (N 17,702,160, prime factor 257 ≡ 1 mod 4 but ≡ 2 mod 3) is only reachable with k = 4.

## Tools (built in scratchpad, same sources as the repo)

- `research/structured/haar_sym.c`: `gcc -O3 -march=native -fopenmp`.
- Checkers: `research/frontier/haarcheck_sl.c`, `research/frontier/haarcheck2.c` (SL(2,p) × Z_n above 20M),
  `research/structured/tools/haarcheck_psl.c` (PSL(2,p) × Z_n above 20M).
- Screen: `research/structured/tools/orb_screen.py 12 9 LO HI "k m f" --samples S --bin <haar_sym>`.

## Log

### Setup (01:20–01:30 UTC, 2026-10-26)
- Checkers rebuilt; haarcheck_psl re-validates the round-2 record (VALID, N 17,696,952, ecc 9).
- orb_screen (k=3 filter, k=4 with --anyn) running on the range above; results in the scratchpad screen/ dir.
- k=4 screen on sl 41×Z257 (N 17,702,160) and psl 49×Z301: random-S minimum about 2,300 and 2.5 million, far above the
  k=3 leads (min 22–58). Dropped; k=4 is not competitive for these groups.
- k=3 screen (300 random S, range 17.70M–17.90M, prime-filtered n), ranked by p1/p10 of cost:
  sl 83×31 (N 17,722,824, μ 29.5, Fix 83, min 22, p1 34), psl 61×157 (17,813,220, μ 31.8, Fix 29, min 45, p1 54),
  sl 49×151 (17,757,600, μ 30.4; prime power 49, no checker), psl 81×67 (17,800,560; prime power 81, no checker),
  psl 47×343 (17,797,584, μ 31.4, Fix 23, min 58), sl 41×259 (17,839,920, μ 32.4, Fix 41, min 42), sl 43×223 (min 48),
  psl 49×301 (17,698,800; prime power 49, no checker).

### Batch 1 (started ~01:25 UTC, 2 h each), progress at t ≈ 3,075 s
- sl 83×31 seed 3: best 6 at 81.6k evals. Same value at 40k evals (t 1,570), so no progress in the last 25 min.
- sl 43×223 seed 3: best 12 at 85.9k evals (stuck since ~50k).
- psl 47×343 seed 3: best 18 at 90.6k evals (stuck since ~45k).
- psl 61×157 seed 1 (N 17,813,220, μ 31.8) started 02:17 UTC, 2 h, on the core freed by the screen.

### Batch 1 result (03:25 UTC)
- sl 83×31 seed 3: **solved** at 184k evals → record 35,445,648 (see RECORD above).
- psl 47×343 seed 3 (N 17,797,584): unsolved, best 6 at 211k evals (2 h).
- sl 43×223 seed 3 (N 17,720,472): unsolved, best 12 at 198k evals (2 h). Now below the bar, so no further runs.

### Batch 2 (bar N > 17,722,824), started 03:23–03:30 UTC, 2 h each
- sl 41×259 seed 1 (N 17,839,920, μ 32.4): started 03:23, best 42 at 4k evals at first check.
- psl 61×157 seed 1 (N 17,813,220): best 12 at 76k evals (t 4,110 s).
- sl 61×79 seed 1 (N 17,926,680, μ 34.8): started 03:25, best 94 at the first check.
- psl 47×343 seed 4 (N 17,797,584): started 03:26, best 86 at the first check.
