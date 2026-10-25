# Cell (Δ, D) = (9, 8): raise-9-8 job (Haiku worker)

Branch `claude/raise-d9d8-haar-record-rqmcq3`. Brief: raise our own (9,8) record above 540,360 vertices (N = |G| = 270,180,
psl 19 × Z79, orbit search k = 3, m = 3, f = 0; solution research/frontier/sols/d9D8_psl_19_79_orb3_s1.txt, rebuilt by
research/structured/runs/d9D8_psl_19_79_orb3_s1.log). Table value 449,480. Bipartite Moore bound 4,793,490.

## Status (updated as the job runs)

- 2026-10-25: started. `research/structured/haar_sym` compiled (gcc -O3 -march=native -fopenmp, as in its README).
- Next group orders: the record is the last one at N ≤ 270,180 of the orbit recipe. Every N above it is a new record.
- Target: an N whose orbit annealing reaches cost 0. The record took 4.4·10⁵ evals (99 s, 1 thread) at μ = 37.9.

## Method

Poisson model (SIZE_LAW.md, STRUCTURE.md §1–3): W = 2,396,745 binding words at (9,8), λ = W/N, μ = N e^(−λ).
k = 3 orbit search, f = 0 (Δ = 3·3). μ/3 + |Fix(α)|·e^(−λ/3) is the effective mean. Screening with
`research/structured/tools/orb_screen.py 9 8 270181 300000 "3 3 0" --samples 300 --nmax 2000` (RANDORB random-S
statistics; result in the scratchpad screen file). Random-S median on the record group is 114 (p1 36, p10 57 at μ 37.9).

Candidates above the record (μ at N, RANDORB median):

| group | N | μ | |Fix| | random median | note |
|---|---|---|---|---|---|
| psl 7 × Z1609 | 270,312 | 38.1 | 2 | 5,478 | 40 s: best 198. Dead end |
| sl 16 × Z67 | 273,360 | 42.6 | 14 | 121 | wave 1 |
| prod sl 5 × sl 5 × Z19 | 273,600 | 42.9 | 35 | 331 | wave 1 |
| sl 13 × Z127 | 277,368 | 49.0 | 11 | 244 | wave 1 |
| pgl 16 × Z67 | 273,360 | 42.6 | 14 | 126 | wave 1 |
| sl 8 × Z547 | 275,688 | 46.2 | 8 | 578 | not yet |
| psl 11 × Z421 | 277,860 | 49.9 | 5 | 432 | not yet |
| sl 11 × Z211 | 278,520 | 51.0 | 11 | 269 | not yet |
| psl 13 × Z259 | 282,828 | 59.0 | 5 | 354 | not yet |

## Runs

Job files and logs: `research/structured/runs/raise_d9D8/` (queue logs per group; logs `d9D8_<group>_orb3f0_s1.log`).
The pool wrapper `tools/pool.sh` needs `orbq.sh` to be executable, which it is not in this checkout, so the queue
scripts were launched with `bash tools/orbq.sh JOBS OUTDIR` directly.

| group | N | seconds | seed | result |
|---|---|---|---|---|
| psl 7 × Z1609 | 270,312 | 40 (stopped) | 1 | best 198 |
| sl 16 × Z67 | 273,360 | 900 | 1 | best 3 (4.0·10⁶ evals), not solved |
| prod sl 5 × sl 5 × Z19 | 273,600 | 900 | 1 | best 4 (3.3·10⁶ evals), not solved |
| sl 13 × Z127 | 277,368 | 900 | 1 | best 6 (4.6·10⁶ evals), not solved |
| pgl 16 × Z67 | 273,360 | 900 | 1 | best 3 (3.9·10⁶ evals), not solved |
| sl 16 × Z67 | 273,360 | 3600 | 2 | best 1 (1.6·10⁷ evals), not solved; one fixed point left |
| sl 16 × Z67 | 273,360 | 3600 | 3 | best 1 (1.6·10⁷ evals), not solved |
| sl 16 × Z67 | 273,360 | 3600 | 3, ORBW=3 | best 3 (1.6·10⁷ evals), not solved |
| sl 16 × Z67 | 273,360 | 3600 | 4 | best 3 (1.6·10⁷ evals), not solved |
| sl 16 × Z67 | 273,360 | 3600 | 4, ORBW=3 | best 3 (1.6·10⁷ evals), not solved |

## Conclusion so far (2026-10-25, about 2.5 h in)

Twelve orbit runs above the record order, N = 270,312 to 277,860, none solved. Best costs: 1 (sl 16 × Z67, 1 h,
two seeds), 3, 4, 6, 16, 37 for the others. The record's order was solved in 4.4·10⁵ evals at μ 37.9; the
candidates tried sit at μ 42–50 and need at least 10⁷ evals, which is 10–30 min per run on this box. The three
1-h sl 16 × Z67 runs show a stall at cost 1–3 (fixed points of α left uncovered), the same pattern as
(10,8) and (11,8) in STRUCTURE.md §7. This is not a proof that the cell cannot move, but in this session the
orbit method with k = 3, f = 0 did not reach the next group order. Options the coordinator can decide on:
(a) hours more per candidate (sl 16 × Z67 is the closest), (b) k = 5 orbit search on a group with few fixed
points (STRUCTURE.md §7), (c) a bigger model or a squad run (haiku-squad) on this cell.
| sl 8 × Z547 | 275,688 | 1800 | 1 | best 37 (7.7·10⁵ evals), not solved |
| psl 11 × Z421 | 277,860 | 1800 | 1 | best 16 (9.7·10⁵ evals), not solved |

Reading after wave 1: all three finished runs stalled at cost 3–6 (one to two uncovered orbits or fixed points).
The record at μ 37.9 needed only 4.4·10⁵ evals, so the step from μ 38 to μ 42–50 costs much more than
10× in evals. Groups with μ ≈ 38–41 above the record are poor on random-S statistics (psl 7 × Z1609, psl 9 × Z751,
prod psl 3 × psl 3 × Z1879), so the small steps are not reachable by this orbit recipe at the current budget.

## Notes for a resumed session

- Thread count: THREADS=1, nice, at most 4 jobs in parallel (4 cores).
- A solved job is checked by build_haar2.py (N ≤ 10M) by orbq.sh; a new record also needs an all-pairs check by
  the coordinator, so save the file in research/frontier/sols/ with the name d9D8_<group>_orb3f0_s<seed>.txt.
- Do not use rm with shell-variable paths in commands (blocked by the safety check).
