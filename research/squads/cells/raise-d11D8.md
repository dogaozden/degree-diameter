# raise-d11D8, round 3: beat 2,258,520 at (Δ, D) = (11, 8)

Job "raise3-11-8" (Haiku worker, cloud session, started 2026-10-26 ~01:15 UTC; budget 6 h, until ~07:15 UTC).
Record to beat: 2,258,520 = 2·|PSL(2,59) × Z_11| (N = 1,129,260), `research/frontier/sols/d11D8_psl_59_11_orb5_ORBW5_s3.txt`.
Only a Haar graph with N > 1,129,260 can beat it (2N > 2,258,520).

Round 1 (`claude/raise-d11d8-record-b63gz5`) and round 2 (`claude/raise-d11d8-resume-b20o9t`, notes copied to
`research/squads/cells/raise-d11D8_round2.md`) are not repeated here. In short:
- Round 1 screened all 60 groups with N in (1,129,260, 1,200,000] at k = 5 (`orb_screen.py`, 400 samples). Only
  psl 19 × Z331 (min 37), sl 16 × Z281 (min 52) and psl 11 × Z1721 (min 76) are above the record in N and competitive
  at all. Every other group is worse. Round 2 checked the four order-5 residues r for psl 19 × Z331 (same statistics).
- Round 1 and round 2 on psl 19 × Z331: about 17 annealing runs, none reached cost 0. Best raw cost 1 (round 2, seed 23,
  1.46M evals). Its exhaustive single-slot scans (EXH) at energy 5 found no better orbit, so that state is a strict local
  minimum for one-orbit moves. The state was never saved, so it cannot be restarted from.
- Round 2's EXH scans cost about 15 min each, and the run rate dropped to about 135 evals/s. Plain annealing ran at
  about 158 evals/s in this container on a 60 s smoke test (round 2's record run had 375/s). Round 2 found the
  scans only pay off after the best energy improves, so the scans are not the main lever.
- k = 2 (involutions) and k = 3 are ruled out for this Δ and μ: `research/structured/STRUCTURE.md` §2–3 and §5. For k = 3,
  μ/3 ≈ 21 at N ≈ 1.13M, above the k = 3 wall (μ_eff ≈ 16–18). k = 10 with one orbit (m = 1) has ~10⁵ candidate S, far
  below the first-moment threshold.

## Round 3 plan

Round 3 does not repeat the EXH scans or the seed-23 scan. It runs the record's own plain procedure on psl 19 × Z331,
the only group above the record that is competitive, on new seeds, with the best state saved.

- Change in `research/structured/haar_sym.c`: `DUMP=<file>` writes the best S (d element ids) whenever the energy
  improves. Default output is unchanged. Binary `haar_sym_r3` (gcc -O3 -march=native -fopenmp).
- Runs (`research/structured/runs/raise11_8_r3/launch.sh`): `ORBIT="5 2 1" ORBW=5 K=8 THREADS=1`, no EXH, no RESTART,
  seeds 31–34, 9600 s each, started 01:20 UTC. Logs `runs/raise11_8_r3/psl19_331_s<seed>.log`, dumps `.dump`.
- Any cost-0 result is written to `research/frontier/sols/d11D8_psl_19_331_orb5_R3_s<seed>.txt` by haar_sym's own
  full check, then goes through `build_haar2.py` (N ≤ 20M) before it counts.

## Log

- 01:15 UTC: session start. Read round-1 and round-2 notes, the seed-23 log, and the orb_screen candidate list.
- 01:19 UTC: DUMP hook added to `haar_sym.c` (default path unchanged); built `haar_sym_r3`. Smoke test (60 s, seed 31):
  158 evals/s, no errors.
- 01:20 UTC: four plain runs started (seeds 31–34, 9600 s each).
- 04:00 UTC: seeds 31–34 finished (9600 s each, about 1.63M evals). Best raw costs 10, 6, 10, 10. No solution.
  The plateau at energy 10 seen in round 2 appears again. Logs and best-state dumps (`runs/raise11_8_r3/*.dump`) are
  committed with `git add -f`; the live logs are no longer tracked while runs are running.
- 04:02 UTC: second batch, seeds 35–38, 9000 s each, same command (`launch2.sh`).
- 06:31 UTC: batch 2 (seeds 35–38, 9000 s each, about 1.47M evals) finished. Best raw costs 10, 10, 10, 10. No solution.

## Final status (06:31 UTC): not beaten

No run found a cost-0 orbit set for any group with N > 1,129,260. The record 2,258,520 stands.

| run | group | budget | evals | best cost |
|---|---|---|---|---|
| r3 seed 31 | psl 19 × Z331 | 9600 s | 1.63M | 10 |
| r3 seed 32 | psl 19 × Z331 | 9600 s | 1.64M | 6 |
| r3 seed 33 | psl 19 × Z331 | 9600 s | 1.64M | 10 |
| r3 seed 34 | psl 19 × Z331 | 9600 s | 1.64M | 10 |
| r3 seeds 35–38 | psl 19 × Z331 | 9000 s | ~1.47M each | 10, 10, 10, 10 |

Across rounds 1–3: 21 plain or near-plain annealing runs (and the round-2 EXH runs) on psl 19 × Z331, best raw cost 1
(round 2, seed 23, one uncovered α-fixed element). Nothing in round 3 reached cost 0.

## Why I stopped

- Every group above the record that is competitive has been screened (round 1, all 60 candidates at k = 5) and
  psl 19 × Z331 is the only one close enough to try. The others have worse random-sample statistics (min ≥ 52).
- k = 2 and k = 3 are ruled out for this (Δ, μ) (`research/structured/STRUCTURE.md`); k = 10 with one orbit has too few
  candidates.
- The annealer plateaus at energy 10 on psl 19 × Z331 in most runs, and 8 more seeds in round 3 did the same. More seeds
  on this group are a long shot with no change in method. I judge this cell will not move further with these methods in
  this budget. The one thing that could change that is a new search method (for example a two-slot move or a faster
  evaluator), not more of the same.

## Next steps if someone resumes

1. A two-slot exhaustive move from the best saved state (`runs/raise11_8_r3/psl19_331_s32.dump`, cost 6), to test whether
   the plateau has a neighbour one step further out.
2. A faster evaluator (the record run ran at about 375 evals/s, this container at about 170), which would double the seeds.
