# raise-d13D9: raising the (13,9) record (bipartite, Δ = 13, D = 9)

Record to beat: **67,742,688** vertices = 2·|SL(2,103) × Z_31| (N = 33,871,344), Haar graph, k = 3 orbit search
(m = 4 free orbits, f = 1), found in the structured-search session (branch `claude/structured-search-orbit-04hefm`,
`research/structured/runs/d13D9_sl_103_31_orb3_s1.log`: μ = 32.8, μ_A ≈ 12.9, 10,713 evaluations, 1,928 s on one thread).

## Method

- Tools: `haar_sym.c` (orbit search, k = 3, f = 1, `ORBIT="3 4 1"`) and `tools/plan_orbit.py` from
  `research/structured` on branch `claude/structured-search-orbit-04hefm` (commit 03050f1b14). Built locally with
  `gcc -O3 -march=native -fopenmp`; low-memory checkers `haarcheck_sl.c` and `haarcheck2.c` (for N > 10M).
- Smoke test: sl 101 × Z_31 (the old (13,9) record, 63,872,400) solved again in 321 evaluations / 23 s with seed 1,
  and `haar_sym` reports a full diameter check.
- Runs: `pool.sh` with 4 single-thread slots, `orbq.sh` per job (builds `d13D9_<group>_orb3_s<seed>.txt`, log, checkpoint).
- Planner (window 2N ∈ [67,742,689, 90,000,000], SL only at odd D, k = 3 and 5, conj and Frobenius): the candidates
  with μ_A ≤ 14 are
  | group | 2N | μ | μ_A | predicted evals |
  |---|---|---|---|---|
  | sl 53 × Z_229 | 68,161,392 | 35.9 | 12.70 | 8.6e4 |
  | sl 61 × Z_151 | 68,529,840 | 38.9 | 13.76 | 1.5e5 |
  | sl 89 × Z_49  | 69,078,240 | 43.7 | 15.72 | 3.9e5 |
  | sl 59 × Z_169 | 69,398,160 | 46.7 | 16.42 | 5.5e5 |
  Everything else in the window has μ_A ≥ 16 (more than ~10⁶ evaluations, days on one core).
  The planner's prediction is pessimistic: on the (13,9) runs so far it over-predicts by 5–10×.

## Runs (round 1, 2 h per job)

| job | N | evals (2 h) | best cost | result |
|---|---|---|---|---|
| sl 53 × Z_229, seed 1 | 34,080,696 | 48,625 | 24 | no solution |
| sl 53 × Z_229, seed 2 | 34,080,696 | 49,081 | 12 | no solution |
| sl 61 × Z_151, seed 1 | 34,264,920 | 27,913 | 20 | no solution |
| sl 89 × Z_49, seed 1 | 34,539,120 | 53,417 | 14 | no solution |

Round 2 (09:42–11:42, 2 h each), no solution:
| job | evals | best cost |
|---|---|---|
| sl 53 × Z_229, seed 3 (RESTART=1) | 40,457 | 24 |
| sl 53 × Z_229, seed 4 | 40,881 | 24 |
| sl 53 × Z_229, seed 5 (RESTART=1) | 40,121 | 18 |
| sl 89 × Z_49, seed 2 | 45,273 | 16 |

Round 3 (11:42, 1.5 h each): sl 53 × Z_229 seeds 6 and 7 (RESTART=1); sl 89 × Z_49 seed 3; sl 59 × Z_169 seed 1 (μ_A 16.4).
Costs were flat for the last hour in most runs. The 103 record needed about 10k evaluations, so 2 h at 0.18 s per
evaluation (about 40k evaluations) is not yet decisive for these groups.

## Status

- Round 1 (07:41–09:41): no solution. Round 2 started 09:42.

## Notes for a resume

- Re-start with `tools/pool.sh DIR 4` after the job files are in place; `orbq.sh` resumes from checkpoints.
- Any VALID file goes to `research/frontier/sols/d13D9_*.txt` after `haarcheck_sl` and `haarcheck2` (N > 20M)
  or `build_haar2.py` (N ≤ 20M) agree.
