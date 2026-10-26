# Raise the (Δ,D) = (12,9) record, round 3 (Haar graphs)

Job "raise3-12-9", Haiku worker, branch `claude/raise-d12d9-bipartite-round3-fhhyi9`.
Round 2 is on `claude/raise-d12d9-bipartite-record-b26a5o` (notes `research/squads/cells/raise-d12D9-round2.md`
there). Round 1 is on `claude/raise-d12d9-bipartite-record-f510kc`.

## Bar to beat

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
