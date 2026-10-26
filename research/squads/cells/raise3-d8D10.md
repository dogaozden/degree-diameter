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
