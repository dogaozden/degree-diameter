# Cell (Δ, D) = (10, 10): raise the record above 60,141,120

Job "raise-10-10" (Haiku worker, cloud session, branch `claude/raise-d10-d10-record-pyapvk`, 2026-10-25).

Table value 50,331,156. Our record 60,141,120 = 2N with N = |SL(2,79) × Z_61| = 30,070,560, k = 3, m = 3, f = 1
(`../../frontier/sols/d10D10_sl_79_61_orb3_s1.txt`, found by the structured search, μ = 15.3, 833 evaluations).
Moore bound 871,696,100. W(10,10) = 435,848,050, so λ = W/N ≈ 14.5 at N ≈ 30M.

## Plan

- μ = N·exp(−W/N) is the planning variable (`../../structured/tools/mu_plan.py`). Reference points for the 2N target:
  μ = 20 ↔ 2N ≈ 61.2M, μ = 25 ↔ 62.1M, μ = 30 ↔ 62.9M, μ = 35 ↔ 63.5M, μ = 40 ↔ 64.1M.
- k = 3 (m = 3, f = 1): the record recipe. Fitted cost grows like e^(μ/4.5) evaluations (STRUCTURE.md §3).
- k = 5 (m = 2, f = 0; 10 = 5·2, so no identity letter): μ_eff = μ/5 + |Fix|·e^(−λ/5). With |Fix| ≈ q ≈ 60–80 this
  is about 8–9 at μ ≈ 30–40, where k = 3 is at μ_eff ≈ 11–14. It is the route to μ > 35 if the fit holds.
- Tools: `../../structured/haar_sym` (built from haar_sym.c with `gcc -O3 -march=native -fopenmp`), THREADS=1, nice,
  timeout. Verifiers: `../../structured/tools/hcsl` and `hc2` (SL, > 20M), `haarcheck_psl` (PSL, > 20M), and
  `../../frontier/build_haar2.py` (≤ 20M). Built from the checked-in sources.

## Screens (RANDORB, 150 random symmetric S per group, cost statistics only)

All 142 groups with μ ≤ 36 (k = 5, f = 0, 67 groups) or 17 ≤ μ ≤ 26 (k = 3, f = 1, 75 groups) in N ∈ [30.0M, 34.0M].
Median random cost, the best few:

| k | group | N | μ | |Fix| | min | p1 | median |
|---|---|---|---|---|---|---|---|
| 3 | sl 163 × 7 | 30,314,088 | 17.3 | 161 | 3 | 5 | 22 |
| 3 | sl 89 × 43 | 30,309,840 | 17.2 | 89 | 3 | 6 | 23 |
| 3 | prod psl 3 × psl 73 × 13 | 30,337,632 | 17.5 | 107 | 4 | 5 | 28 |
| 3 | psl 97 × 67 | 30,571,296 | 19.7 | 47 | 6 | 9 | 30 |
| 3 | psl 73 × 157 | 30,532,104 | 19.3 | 35 | 9 | 12 | 33 |
| 3 | sl 73 × 79 | 30,726,576 | 21.2 | 71 | 11 | 12 | 34 |
| 5 | sl 79 × 61 (the record group, as a control) | 30,070,560 | 15.3 | 79 | 4 | 5 | 27 |
| 5 | psl 125 × 31 | 30,271,500 | 16.9 | 124 | 6 | 9 | 28 |
| 5 | psl 61 × 271 | 30,747,660 | 21.5 | 29 | 9 | 11 | 38 |
| 5 | prod psl 11 × psl 11 × 71 | 30,927,600 | 23.4 | 24 | 6 | 7 | 38 |
| 5 | psl 101 × 61 | 31,421,100 | 29.7 | 49 | 7 | 16 | 40 |
| 5 | sl 59 × 151 | 31,003,320 | 24.3 | 59 | 12 | 12 | 45 |
| 5 | psl 179 × 11 | 31,543,380 | 31.5 | 89 | 7 | 10 | 46 |

Reading: at these μ the k = 5 random costs are not clearly better than k = 3 (the control, sl 79 × 61 at k = 5, has
median 27 against 30 at k = 3). So the random-S screen does not settle it; the orbit search does.
Products (prod …) are not used for records above 20M: no low-memory checker exists for them.

## Searches launched (orbq.sh, 4 queues, THREADS=1)

Job files and logs: `../../structured/runs/raise-d10D10/` (`jobs_{a,b,c,d}.txt`, `queue_*.err`, one log per job).

- a: k = 3, f = 1, sl 163 × 7, μ 17.3, 1200 s (a cheap rung; would give 60,628,176 if solved)
- b: k = 5, f = 0, psl 101 × 61, μ 29.7, 3600 s (the main attempt above μ = 25)
- c: k = 5, f = 0, psl 61 × 271, μ 21.5, 1800 s
- d: k = 5, f = 0, sl 59 × 151, μ 24.3, 2400 s

## Records

- **61,495,320** (+2.3 % over 60,141,120): PSL(2,61) × Z_271, k = 5, m = 2, f = 0, μ = 21.5, |Fix| = 29, 1,217 evaluations
  (orbit search, 78 s). File `../../frontier/sols/d10D10_psl_61_271_orb5f0_s1.txt`. Checked by `tools/haarcheck_psl`
  (independent low-memory BFS from (e,A) and (e,B): all 30,747,660 elements reached within 10, 31 s) and by haar_sym's
  own full check. build_haar2.py was not run (hours and > 7 GB above 20M vertices).
  Log: `../../structured/runs/raise-d10D10/d10D10_psl_61_271_orb5f0_s1.log`.

- **62,006,640** (+3.1 % over 60,141,120, +0.8 % over 61,495,320): SL(2,59) × Z_151, k = 5, m = 2, f = 0, μ = 24.3,
  |Fix| = 59, 16,497 evaluations (1,468 s, one thread). File `../../frontier/sols/d10D10_sl_59_151_orb5f0_s1.txt`.
  Checked by `tools/hcsl` and `tools/hc2` (both SL low-memory checkers, both BFS: diameter 10, all vertices reached)
  and by haar_sym's own full check. Log: `../../structured/runs/raise-d10D10/d10D10_sl_59_151_orb5f0_s1.log`.

- **62,842,200** (+4.5 % over 60,141,120, +1.3 % over 62,006,640): PSL(2,101) × Z_61, k = 5, m = 2, f = 0, μ = 29.7,
  |Fix| = 49, 32,761 evaluations (2,264 s). File `../../frontier/sols/d10D10_psl_101_61_orb5f0_s1.txt`. Checked by
  `tools/haarcheck_psl` (both BFS: diameter 10, all 31,421,100 elements reached) and by haar_sym's full check.
  Log: `../../structured/runs/raise-d10D10/d10D10_psl_101_61_orb5f0_s1.log`.

- **63,764,520** (+6.0 % over 60,141,120, +1.5 % over 62,842,200): PSL(2,61) × Z_281, k = 5, m = 2, f = 0, μ = 36.9,
  |Fix| = 29, ORBW = 5 (an uncovered fixed element weighs as much as a free orbit), seed 2, 9,177 evaluations (606 s).
  File `../../frontier/sols/d10D10_psl_61_281_orb5f0_ORBW5_s2.txt`. Checked by `tools/haarcheck_psl` (both BFS:
  diameter 10, all 31,882,260 elements reached) and by haar_sym's full check.
  Log: `../../structured/runs/raise-d10D10/d10D10_psl_61_281_orb5f0_ORBW5_s2.log`.
  The same group with seed 1 and no ORBW ended at cost 1 after 38,217 evaluations (no solution, 2,499 s).

- Also solved, not a record: PSL(2,179) × Z_11, k = 5, f = 0, μ = 31.5, 44,401 evaluations, 63,086,760 vertices
  (`../../structured/runs/raise-d10D10/d10D10_psl_179_11_orb5f0_s1.log`; solver check only, not recorded).

- **63,854,520** (+6.2 % over 60,141,120, +0.1 % over 63,764,520): PSL(2,59) × Z_311, k = 5, m = 2, f = 0, μ = 37.6,
  |Fix| = 29, ORBW = 5, seed 2, 27,737 evaluations (1,879 s). File `../../frontier/sols/d10D10_psl_59_311_orb5f0_ORBW5_s2.txt`.
  Checked by `tools/haarcheck_psl` (both BFS: diameter 10, all 31,927,260 elements reached) and by haar_sym's full check.
  Log: `../../structured/runs/raise-d10D10/d10D10_psl_59_311_orb5f0_ORBW5_s2.log`.
  The same group with seed 1 and no ORBW also solved later (72,641 evaluations, 4,849 s) at the same order, 63,854,520:
  an equal-size second solution (`d10D10_psl_59_311_orb5f0_s1.txt`), not a further record.

## Where it stands (2026-10-25, 11:15)

Record: **63,854,520** (PSL(2,59) × Z_311, k = 5, ORBW = 5). Verified by haarcheck_psl. Not run: build_haar2.py (hours,
> 7 GB at this size); the coordinator should decide whether to run it.

Stopped, and why: the k = 5 route is at its wall for this cell.
- Every pure group (SL/PSL of prime q with 5 | q ± 1, prime factors of n ≡ 1 mod 5) with μ ≤ 37.6 in N ∈ [30.0M, 32.0M] has
  been tried; the solved ones are the records above (μ 21.5 → 37.6).
- The next band is μ ≈ 46: PSL(2,71) × Z_181 (N = 32,384,520, μ 46.3) failed twice with 2 h each (best 10 for seed 1,
  best 5 for seed 2, ORBW = 5).
- Higher orders have μ > 50 (for example PSL(2,109) × Z_101, μ ≈ 54), which the k = 3 and k = 5 random-cost evidence does
  not support. Product groups were not used for records (no low-memory checker above 20M).
- Not tried: k = 7 (needs f = 3 extra torus letters, the known collision problem), SL(3,q) (not implemented), and
  voltage lifts (a different program).

## Status log

- 2026-10-25 07:20: started. Compiled haar_sym and the three checkers. Screens launched.
- 07:23–07:53: screens finished (see table). Queues a–d launched at 07:54.
- 07:55: c (psl 61 × 271, k = 5) solved at μ = 21.5 → 61,495,320 (new record, checked above).
- 07:57: queue a (sl 163 × 7, μ 17.3) stopped: below the new record. Queues e (psl 179 × 11, μ 31.5) and f (psl 61 × 281, μ 36.9) launched.
- 08:19: d (sl 59 × 151, k = 5) solved at μ = 24.3 → 62,006,640 (checked by hcsl and hc2 above).
- 08:27: g (psl 61 × 281, ORBW=5, seed 2) launched. The seed-1 run of psl 61 × 281 (no ORBW) was stuck at cost 1 after 27k evaluations.
- 08:32: b (psl 101 × 61, k = 5, μ 29.7) solved → 62,842,200 (checked by haarcheck_psl above).
- 08:33: h (psl 59 × 311, k = 5, μ 37.6, 7200 s) launched.
- 08:38: g (psl 61 × 281, ORBW=5, seed 2) solved → 63,764,520 (checked by haarcheck_psl above).
- 08:39: i (psl 59 × 311, ORBW=5, seed 2, 7200 s) and j (psl 71 × 181, ORBW=5, seed 1, 7200 s) launched.
- 08:50: e (psl 179 × 11) solved → 63,086,760, below the record.
- 09:11: i (psl 59 × 311, ORBW=5, seed 2) solved → 63,854,520 (checked by haarcheck_psl above). Queues h (no ORBW) and j (psl 71 × 181) still running.
- 09:54: h (psl 59 × 311, seed 1, no ORBW) solved at the same order, 63,854,520 (second solution, not a record). j and k (psl 71 × 181, seeds 1 and 2) still running.
- 10:39: j (psl 71 × 181, ORBW=5, seed 1, μ 46.3, 7200 s) ended at best cost 10 after 95,617 evaluations. Not solved.
- 11:12: k (psl 71 × 181, ORBW=5, seed 2) ended at best cost 5 after 95,409 evaluations. Not solved. No search running.

---

# Round 2 (branch `claude/raise-d10-d10-round-2-y1a306`, started 2026-10-25 14:15 UTC)

Starting point: the round-1 record **63,854,520** (PSL(2,59) × Z_311, k = 5, ORBW = 5, file
`../../frontier/sols/d10D10_psl_59_311_orb5f0_ORBW5_s2.txt`). The round-2 brief said 60,141,120; that is the
pre-round-1 value, so round 2 targets anything above 63,854,520 (N > 31,927,260).

## What round 1 left open (read from its notes)

- Route with k = 5 (Δ = 5·2, f = 0). Solved up to μ = 37.6. μ = 46.3 failed on psl 71 × 181 (two seeds, 2 h each, best 10
  and 5; cost 5 with ORBW = 5 is one uncovered orbit or one fixed point).
- Not tried by round 1: other groups with N in (31.93M, 32.5M); k = 7 (f = 3 collisions); SL(3,q); voltage lifts.

## Candidates (N just above 31,927,260; k = 5, f = 0)

Group validity: k = 5 needs 5 | |Q|, so PSL(2,q) with q ≡ ±1 mod 5. Fix = |C_Q(α)| × gcd(r−1, n), so PSL(2,q)
gives |Fix| ≈ (q ± 1)/2 (smallest for the torus that contains the order-5 element).

| group | N | μ | |Fix| | RANDORB 1000 samples: min / p1 / p10 / median | note |
|---|---|---|---|---|---|
| psl 79 × 131 | 32,288,880 | 44.3 | 39 | 10 / 24 / 37 / 62 | new group; record group's control (psl 59 × 311) is min 16, p1 20, median 61 |
| psl 71 × 181 | 32,384,520 | 46.3 | 34 | 12 / 29 / 43 / 69 | round 1's group, 2 seeds failed (best 5, 10) |
| psl 41 × 941 | 32,408,040 | 46.8 | 19 | 20 / 37 / 57 / 105 | large cyclic factor: poor |
| psl 31 × 2161 | 32,155,680 | 41.8 | 14 | 40 / 56 / 80 / 151 | large cyclic factor: poor |
| sl 101 × 31, pgl/sl 47 × 311 | 31.9–32.3M | 37.8–44 | 99 / – | invalid or bad (sl 101 × 31: median 60, fix 99; the 47 × 311 groups have no element of order 5) | dropped |

Screen with `tools/orb_screen.py` (`--list`, then RANDORB) is a weak signal on its own: the record group itself has median 61.
Candidates were chosen by min/p1 and by |Fix|, then tested with the orbit search.

## Searches (orbq.sh, 4 queues, THREADS = 1, 10,800 s each)

Job files and logs: `../../structured/runs/raise-d10D10-r2/` (`jobs_{a,b,c,d}.txt`, `queue_*.err`, one log per job).

- a: k = 5, f = 0, ORBW = 5, psl 79 × 131, seed 1
- b: k = 5, f = 0, ORBW = 5, psl 79 × 131, seed 2
- c: k = 5, f = 0, ORBW = 5, psl 71 × 181, seed 3
- d: k = 5, f = 0 (no ORBW), psl 79 × 131, seed 3

## Status log

- 2026-10-25 14:25 UTC: searches a–d launched.
- 2026-10-25 15:55 UTC: no solution yet. Best costs after 40–67k evals (~0.11 s/eval with 4 jobs): psl 71 × 181 seed 3: 5;
  psl 79 × 131 seed 2 (ORBW 5): 5; seed 1 (ORBW 5): 6; seed 3 (no ORBW): 6. Cost 5 = one uncovered orbit or one fixed point.
- 2026-10-25 16:25 UTC: a mistake: `kill` by the pattern "10800 3 8" also stopped psl 71 × 181 seed 3 (log ends at best 5,
  89,849 evals, not a full 3 h). Both seed-3 jobs were stopped at 2 h (psl 79 × 131 seed 1 at best 6, psl 79 × 131 seed 3
  without ORBW at best 5, 61,857 evals).
- 2026-10-25 16:25 UTC: RESTART=1 (fresh random S at each reheat): psl 79 × 131 seeds 4, 5 stayed at 15 after 20k evals;
  psl 71 × 181 seed 6 at best 6 after 31k. Stopped at 17:05.
- 2026-10-25 17:05 UTC: psl 79 × 131 seed 2 (ORBW 5) still at best 5 after 82k evals (ends 3 h). New runs with ORBW = 10
  (fixed points weigh more): psl 79 × 131 seeds 7 and 8, psl 71 × 181 seed 7, 8000 s each.
- 2026-10-25 19:18 UTC: ORBW = 10 runs ended (8000 s each, 60–100k evals): psl 79 × 131 seed 7 best 5, seed 8 best 10;
  psl 71 × 181 seed 7 best 5. psl 71 × 181 seed 9 (ORBW 5, 8000 s) still running, at best 5 after 73k evals (ends ~19:48).
  No solution in round 2 so far. Record stays **63,854,520** (round 1).

## Where it stands (round 2)

- Total round-2 search: about 10 jobs of 2–3 h on psl 79 × 131 and psl 71 × 181 (N = 32.29M and 32.38M, μ 44 and 46),
  plus two RESTART runs. Total ≈ 0.9M evaluations at N ≈ 32M, no solution. Best cost reached: 5 (one uncovered orbit
  or one fixed point) in 9 runs; never below 5.
- The near misses are structural: the annealing stalls at cost 5 at the same floor for every seed, group, and weight
  (ORBW 1, 5, 10). Round 1 reached the same floor on psl 71 × 181.
- What was not tried: a smarter endgame than annealing (for example, exhaustively scanning one orbit replacement
  around a cost-5 state; one evaluation ≈ 0.1 s, so a full scan of N ≈ 3·10⁷ is out of reach), k = 7 (f = 3 torus letters,
  the known collision problem), SL(3,q) (not implemented), voltage lifts, and prime-power PSL(2,81) × Z121 (no
  low-memory checker for GF(81) at > 20M). PSL(2,41) × Z941 and PSL(2,31) × Z2161 were screened and rejected (large
  cyclic factor: random medians 105 and 151).

## Stop reason

The k = 5, f = 0 route is at its wall for N in (31.93M, 32.4M) with these tools and this budget: every candidate group
tried (psl 79 × 131, psl 71 × 181) stalls at cost 5 after 50–100k evaluations. Gains would need roughly 3–5× more
evaluations per group (≈ 10⁶ in total, 20–30 core-hours at 0.1 s per evaluation), more than one Haiku session has.
Recommendation for the coordinator: a bigger model or a new route (SL(3,q) or endgame search) is worth more than more
seeds of these groups.
