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

- Run D-A (jobs_A, ORBW=5 RESTART=1, seed 4): solved at 314,913 evaluations (2,578 s, one thread), after 2 h-scale
  stall at cost 4 for about 25 minutes. Log: research/structured/runs/d10D9_round2/d10D9_sl_41_61_orb5f0_ORBW5RESTART1_s4.log.
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
