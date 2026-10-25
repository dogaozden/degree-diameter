# Cell (Δ, D) = (10, 9): raise-d10D9, round 2 (Haiku worker)

Branch: claude/raise-d10d9-round2-153lq9. Round 1 notes: research/squads/cells/raise-d10D9.md (branch
claude/raise-d10d9-record-w585yh, copied here). Table value 7,057,400 (DS14v2); bipartite Moore bound 96,855,122.

## Bar

The brief says 8,003,856, but round 1 already holds **8,362,560** (psl 31 x Z281, k=5 f=0, verified by build_haar2.py
and haarcheck_psl, coordinator check pending). Bar used here: beat 8,362,560, i.e. N > 4,181,280 (2N > 8,362,560).

## Round-1 dead ends (do not repeat)

- k=5 f=0 on sl 41 x Z61 (best 2, 3 seeds of 1 h), pgl 41 x Z61 (13), psl 59 x Z41 (5 and 8), k=3 f=1 on psl 61 x Z37
  (12), psl 31 x Z283 (30): all stalled at μ ≈ 41–43, ~5M evaluations total, no solution.
- Round 1 ran no ORBW (fixed-element weight) setting on the stalled runs.

## Round 2 plan

1. Screen (RANDORB=1500, ORBIT="5 2 0") the k=5 groups of the window that round 1 did not run, plus baselines.
   Log: research/structured/runs/d10D9_screen/screen_k5.txt
2. Annealing on the best screened candidates, with ORBW=5 (an uncovered α-fixed element weighs as much as a free
   orbit: the lever that solved (11,8) in STRUCTURE.md §8) and RESTART=1.
3. Verify every find (build_haar2.py up to 20M; haarcheck_psl above that).

## Log

### 2026-10-25 (round 2 start)

- Built haar_sym (gcc -O3 -march=native -fopenmp). 4 cores, 15 GB.
- Window candidates (orb_screen --list, k=5 m=2 f=0, N in (4,181,280, 4,500,000]). Many listed groups have no element
  of order 5 (psl 23, psl 17, psl 13, psl 27, sl 13, sl 32, sl 47, sl 73, sl 25×…, prod with sl 7 / psl 7 / psl 9…) and α would be
  trivial on a factor: excluded.
- Screen, 1,500 random symmetric S each (fix = |Fix(α)|, μ from orb_screen formula):
  - sl 25 x Z271: fix 49, μ 44.8, min 66, p1 124, p10 180, median 428
  - pgl 25 x Z271: fix 24, μ 44.8, min 52, p1 96, p10 186 (median inflated by outliers)
  - psl 19 x Z1231: fix 9, μ 42.5, min 110, p1 191, p10 291 (median 451)
  - psl 25 x Z541: fix 24, μ 43.8, min 38, p1 102, p10 174, median 354
  - psl 59 x Z41: fix 29, μ 42.4, min 23, p1 51, p10 81, median 140 (lowest tail with sl 41 x Z61)
  - sl 41 x Z61: fix 39, μ 41.5, min 20, p1 52, p10 90, median 156
  - sl 16 x Z1031: fix 14, μ 42.1, min 130, p1 196, p10 313 (weak)
  - prod psl 5 psl 5 x Z1171 / Z1181 (A5 x A5, fix 25): stopped after >10 min each (slow evaluator path); not screened
  - Dropped without screening: psl 23/17/13/27, sl 13/32/47/73, prod with sl 7 / psl 7 / psl 9 / sl 3 factors: no element of
    order 5 in a factor, so α is trivial there (STRUCTURE.md §2.2).

- Annealing, 1 h each, 4 in parallel (one core each), ORBW=5 (uncovered fixed element weighs 5; first use on these
  rungs; round 1 ran ORBW=1). Launched 14:23 UTC, jobs in research/structured/runs/d10D9_round2/jobs_{A,B,C,D}.txt:
  - A: sl 41 x Z61, ORBW=5 RESTART=1, seed 4 (round-1 best 2 at cost 1 seed)
  - B: psl 59 x Z41, ORBW=5, seed 5
  - C: psl 59 x Z41, ORBW=5 RESTART=1, seed 3
  - D: psl 25 x Z541, ORBW=5 RESTART=1, seed 1 (μ 43.8, fix 24)
  Note: orbq.sh must be run as `bash tools/orbq.sh` (not executable in this checkout).

### 15:16 UTC: NEW RECORD 8,403,360 (sl 41 x Z61, k=5 m=2 f=0)

- Run D-A (jobs_A, ORBW=5 RESTART=1, seed 4): solved at 314,913 evaluations (2,578 s, one thread), after about 25 minutes at cost 4. Log: research/structured/runs/d10D9_round2/d10D9_sl_41_61_orb5f0_ORBW5RESTART1_s4.log.
- Solution: research/frontier/sols/d10D9_sl_41_61_orb5f0_ORBW5RESTART1_s4.txt. N = |SL(2,41) x Z61| = 4,201,680,
  2N = **8,403,360 vertices**, +0.5 % over 8,362,560 (round 1). μ = 41.5.
- Checks: haar_sym full diameter check OK (both normalisations); build_haar2.py VALID (8,403,360 vertices, 10-regular,
  0 duplicate edges, edge-list sha256 d9b7d3b79cf23fd4dea87cba3e1e17c7f36347a9f58aaac1975379e604b846fd).
- What worked here: ORBW=5 and RESTART=1 together. Round 1's stall on this exact group (best 2, 4 and 2 over 3 seeds
  of 1 h, ORBW=1) did not have these settings. Only one solve, so the effect is not measured.

Window for the next record: N > 4,201,680 (2N > 8,403,360).

Runs still going at 15:20 (1 h each):
- psl 59 x Z41 (N 4,209,060, μ 42.4), ORBW=5 RESTART=1 seed 3: best 2 at 15:06. Round 1's best on this group was 5.
- psl 59 x Z41, ORBW=5, seed 5: best 10.
- psl 59 x Z41, ORBW=5 RESTART=1, seed 6: started 15:20 (jobs_E).
- Stopped: psl 25 x Z541 (best 40, the weakest lead).

### 17:05 UTC: NEW RECORD 8,418,120 (psl 59 x Z41, k=5 m=2 f=0), replaces 8,403,360

- Seed 12 (ORBW=5 RESTART=1), solved at 226,153 evaluations (1,849 s, one thread). Log:
  research/structured/runs/d10D9_round2/d10D9_psl_59_41_orb5f0_ORBW5RESTART1_s12.log
- Solution: research/frontier/sols/d10D9_psl_59_41_orb5f0_ORBW5RESTART1_s12.txt. N = |PSL(2,59) x Z41| = 4,209,060,
  2N = **8,418,120 vertices**, μ = 42.4, |Fix(α)| = 29.
- Checks: haar_sym full diameter check OK (both normalisations); build_haar2.py VALID (8,418,120 vertices, 10-regular,
  0 duplicate edges, edge-list sha256 4fd054322f8ab27f06f42e4673ca5ef6a302a9f258b150fd5a50a644f0d8ccd1).

psl 59 x Z41, all runs (1 h each unless noted), ORBW and RESTART as listed:
- ORBW=1 (round 1): seed 1 best 5, seed 2 best 8.
- ORBW=5: seed 5 best 10; seed 9 best 2 (no solve); seed 11 best 11; seed 13 best 10.
- ORBW=5 RESTART=1: seed 3 best 2; seed 6 best 10; seed 7 best 10; seed 8 best 10 (stopped at 1 h);
  seed 10 best 10; seed 12 **solved**.
- So 1 solve in 12 hour-long runs on this group (round 1's two included).

Dead ends this round: psl 19 x Z1231 (fix 9, best 112 after 9 min), sl 16 x Z1031 (fix 14, best 122 after 9 min),
psl 25 x Z541 (fix 24, best 40 after 1 h). These came from the random screen (min 110 / 130 / 38) and their annealing
never got near the others.

Window for the next record: N > 4,209,060 (2N > 8,418,120).

### 18:15 UTC: stopped. Record 8,418,120 stands.

Last rung tried, N > 4,209,060 (μ 44.8 for the candidates below), 1 h per run, stopped early at about 1 h:
- sl 25 x Z271 (fix 49): seed 1 (ORBW=5 RESTART=1) best 52 at 92,561 evaluations; seed 2 (ORBW=5) best 62 at 53,001.
- pgl 25 x Z271 (fix 24): seed 2 (ORBW=5 RESTART=1) best 32 at 55,697; seed 3 best 40 at 55,441.
- Random-S screen had these at min 66 (sl 25) and min 52 (pgl 25). Round-2 annealing did not get below 32.

**Verdict.** The record moved twice this round (8,362,560 → 8,403,360 → 8,418,120), both by orbit search with
ORBW=5 and RESTART=1 on groups at μ ≈ 41.5–42.4. The next rung (N > 4,209,060, μ ≥ 44) is not reached by the
candidates that remain: their annealing stalls at cost 30–60, far from a solution, within the budget I had.
Round 2 used about 3.5 hours of wall clock and roughly 40 core-hours of search (3–4 cores at a time).

Not tried, if the coordinator wants to go on:
- Longer runs (3–6 h) on psl 59 x Z41 (seeds 3 and 9 reached 2 in 1 h): this would only help a rung above N = 4,209,060 once
  the group is itself the record, so it is not useful now.
- Other elements of order 5 as α: choose_alpha takes the first conjugating element it finds (fixed seed), so every seed in
  this round used the same α per group. ALPHA=<index> would give a different α with the same |Fix|, a cheap way to test
  whether the stall is in α or in S.
- A5 x A5 x Z_n (prod psl 5 psl 5, |Fix| = 25, N = 4,215,600): never run. The orbit evaluator is much slower on this path
  (1500 random samples > 10 min per group), so it needs a long run to tell.
- Nothing else in the window at μ < 44: psl 19 x Z1231, sl 16 x Z1031, psl 25 x Z541 were tried and dropped.

Files this round: research/frontier/sols/d10D9_sl_41_61_orb5f0_ORBW5RESTART1_s4.txt and
research/frontier/sols/d10D9_psl_59_41_orb5f0_ORBW5RESTART1_s12.txt (both VALID by build_haar2.py); logs in
research/structured/runs/d10D9_round2/; screen in research/structured/runs/d10D9_screen/screen_k5.txt.
