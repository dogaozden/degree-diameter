# raise3-d8D10: beat the (8,10) record (job raise3-8-10, branch claude/raise3-8-10-3yy7tc, 2026-10-26)

## Bar (read this first)
- The brief says 7,818,096. That is stale. The round-2 branch (claude/raise2-8-10-record-dmm6z4) holds a
  VERIFIED record of **8,043,840 vertices** = 2·|PROD PSL(2,7) × PSL(2,19) × Z_7|, N = 4,021,920,
  research/frontier/sols/d8D10_prod_psl_7_psl_19_7_orb3_s1.txt (build_haar2.py VALID, 0 duplicate edges).
  Master has no d8D10 record directory yet. So the bar used here is **N > 4,021,920** (vertices > 8,043,840).
- This branch merges claude/raise2-8-10-record-dmm6z4 (sols, logs, cell notes of rounds 1 and 2).

## Round 2 leads (from research/squads/cells/raise-d8D10.md on the merged branch; not repeated)
- Round 2 ran k = 3, f = 2, m = 2 (ORBIT "3 2 2") on prod psl 11×psl 23, prod psl 7×psl 19×Z7 (solved),
  prod psl 3×psl 25×Z43 (7 seeds, best 3), prod psl 7×psl 9×Z67 (best 9), prod sl 5×sl 8×Z67 (best 12),
  sl 3×sl 11×Z127 (stopped at 30), and k = 7 (dead: Δ = 8 forces m = 1, constant cost).
- Cost-3 plateau (one uncovered orbit) is the common wall at μ ≈ 33–41.
- Not run by round 2: prod psl 3 × psl 13 × Z307 (N 4,022,928, μ 33.3) — the nearest candidate above the bar.

## Plan of this round
1. Rank every group in the window N ∈ [4,021,920, 4,070,000] by RANDORB mixing (tools/orb_screen.py, 1500
   samples; the record group has p1 25, p10 43, median 142 as a calibration point).
2. Solver ladder with 3 cores on the best-mixing groups with μ ≤ 34.5; THREADS=1, nice, timeout.
3. Any solve: haar_sym full check, build_haar2.py (≤ 20M), save to research/frontier/sols/d8D10_*.

## Runs
(filled in below as they start)

## Window screen (orb_screen, RANDORB 1500 samples, N in [4,021,920, 4,070,000], ORBIT "3 2 2")
Ranked by (p1+p10)/2 of random symmetric cost. Record group prod psl 7 x psl 19 x Z7 (its N is the bar) = p1 25, p10 43, median 142.
- prod psl 3 x psl 25 x Z43 (4,024,800, μ 33.5): p1 36, p10 69, median 257. Best above-bar group with mixing near the record's.
- prod sl 5 x psl 13 x Z31 (4,062,240, μ 37.6): p1 34, p10 67, median 282. New group (not psl 5 x sl 13).
- prod sl 5 x sl 8 x Z67 (4,052,160, μ 36.5): p1 41, p10 75.
- prod psl 3 x psl 13 x Z307 (4,022,928, μ 33.3): p1 156, p10 504, median 11,846. Big cyclic factor: mixes ~100x worse. DROPPED.
- prod sl 3 x sl 11 x Z127 (4,023,360, μ 33.3): median 1,570. Poor.

## Runs
- Z307 (Q1, Q2): seeds 1, 2 stopped early: best 36 and 40 after 355 s (27k evals). Dead.
- Q3: prod psl 3 x psl 25 x Z43, seed 11, 5400 s.
- Q4: same group, seed 12, ORBW=5, 5400 s.
- Q5: prod sl 5 x psl 13 x Z31 (N 4,062,240, μ 37.6), seed 1, 5400 s.
- Q6: prod psl 3 x psl 25 x Z43, seed 13, RESTART=1, 5400 s.
Logs: research/structured/runs/raise3-d8D10/Q*/.

## Final status of this round (03:45 UTC, 2026-10-26)
- **No record this round.** Bar unchanged: 8,043,840 vertices (N = 4,021,920, prod psl 7 x psl 19 x Z7).
- Runs, all 5400 s, ORBIT "3 2 2", none solved (no sols file written):
  - Q3: prod psl 3 x psl 25 x Z43 (N 4,024,800, μ 33.5), seed 11: best 3 after 6.1e5 evals.
  - Q4: same group, seed 12, ORBW=5: best 3 after 5.7e5 evals.
  - Q6: same group, seed 13, RESTART=1: best 6 after 5.9e5 evals.
  - Q5: prod sl 5 x psl 13 x Z31 (N 4,062,240, μ 37.6), seed 1: best 6 after 7.1e5 evals.
  - Z307 (Q1, Q2, dropped after the screen): best 36 and 40 after 355 s.
- Total this round: about 4 core-hours on 5 seed-runs. Every run ended on the cost-3 or cost-6 plateau (one or two uncovered orbits).
- Psl 3 x psl 25 x Z43 now has 10 seeds in total across rounds 2 and 3 (best 3). Its failure is not bad luck. The ordering
  of random mixing (median 257, p10 69) is similar to the record group's, so the wall is at μ ≈ 33.5 for this family.

## Judgment
- The orbit method (k = 3, f = 2, m = 2) has no unexplored candidate with N in (4,021,920, 4,060,000] and μ ≤ 34 except the
  Z307 group, which mixes about 100 times worse. Within this window the record is at its practical limit for these groups.
- Next rungs (μ ≥ 36) have shown cost 3–9 in every run so far (rounds 2 and 3). Going further needs one of:
  (i) the cheaper orbit evaluation in STRUCTURE.md §7.4 (about +2 in μ) — not applicable to q < 64 groups, so not for the
      record group family;
  (ii) SL(3,q) groups (STRUCTURE.md §7.3) — not implemented; the largest remaining lever;
  (iii) many more seeds on the μ 33–34 groups, which costs about 1.5 core-hours per seed with a success rate near one in five.
- Stopped here: the cell is not going to move with these methods in the time this job allows.
