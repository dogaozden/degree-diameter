# Cell (Δ, D) = (7, 10): raise job, round 2

Haiku worker session on `claude/raise-d7d10-record-r2-5y95db` (2026-10-25). Round 1 is `research/squads/cells/raise-d7D10.md`
(branch `claude/raise-d7d10-record-7d5zrr`), read it first. This file is the round-2 log.

## Record to beat

**2,298,240 vertices** (N = 1,149,120), SL(2,7) × PSL(2,19), no Z factor, k = 3, m = 2, f = 1, seed 2.
File: `research/frontier/sols/d7D10_prod_sl_7_psl_19_1_orb3_s2.txt`. Re-verified here with `build_haar2.py`
(VALID, d = 7, D = 10, n = 2,298,240, 7-regular, no duplicate edges, ~22 s). The brief's 2,237,760 is superseded.

Other verified (7,10) records in this cell (all below the record): 2,277,600 (sl 25 × Z73, pgl 25 × Z73),
2,247,960 (psl 131 × 1), 2,234,400 (psl 49 × Z19; older).

Target for this round: N > 1,149,120 (any group, n prime-compatible with k = 3).

## Where the round-1 route stands

- Round 1 ran the k = 3 orbit ladder over N = 1,118,881–1,200,000 and stopped at the record. Its notes give the wall at μ ≈ 30–34
  for 30–60 min single-core runs. Above N = 1,149,120 nothing was solved (groups listed in round 1's table).
- Round 1 and this round's ranking both suggest that at μ ≈ 31 product groups are the strongest (sampled lower tails), but
  at the same order N = 1,149,120. The same-order product groups (prod psl 7 psl 9 × Z19, prod sl 5 sl 8 × Z19, prod sl 3 sl 19 × Z7)
  cannot beat the record, and the best of them was still at cost 1 after 30 min.

## Candidate screen (round 2, 2026-10-25)

`python3 research/structured/tools/orb_screen.py 7 10 1149000 1172000 "3 2 1" --nmax 5000 --samples 300` (ranking by
sampled p1 cost; full output not committed). Groups above the record order, sorted by p1 (lower is better):

| group | N | μ | |Fix| | min | p1 | median | round 1 result |
|---|---|---|---|---|---|---|---|
| pgl 19 × Z169 | 1,155,960 | 33.1 | 17 | 27 | 48 | 689 | best 12 (30 min, s2) |
| sl 19 × Z169 | 1,155,960 | 33.1 | 17 | 36 | 55 | 313 | best 9 (30 min, s2) |
| prod sl 3 × psl 11 × Z73 | 1,156,320 | 33.2 | 35 | 25 | 62 | 796 | best 13 (30 min) |
| psl 19 × Z337 | 1,152,540 | 32.0 | 8 | 48 | 63 | 659 | best 18 (30 min) |
| sl 16 × Z283 | 1,154,640 | 32.6 | 14 | 60 | 72 | 450 | not tried |
| psl 23 × Z193 | 1,171,896 | 38.7 | 11 | 30 | 45 | 357 | best 6–9 (60–75 min) |

Big cyclic factors (n ≥ 1000, e.g. sl 8 × Z2281, sl 11 × Z871, psl 9 × Z3193) have p1 in the 10³–10⁵ range, and prod-groups
of order 1.15M with n > 1 have p1 ~ 10⁵–10⁶ (fail, not worth runs).

## Runs

Launched 2026-10-25, 4 single-thread runs, `ORBIT="3 2 1"`, K = 8, seed 11, 3600 s budget (logs in `research/structured/runs/`,
prefix `d7D10_`, tag `_orb3_s11`):

| group | N | μ | status |
|---|---|---|---|
| pgl 19 × Z169 | 1,155,960 | 33.1 | running, best 12 at ~9 min (s11) |
| sl 19 × Z169 | 1,155,960 | 33.1 | running, best 16 at ~9 min (s11) |
| sl 16 × Z283 | 1,154,640 | 32.6 | stopped at ~11 min, best 27 (83k evals), no progress after t = 30 s |
| psl 19 × Z337 | 1,152,540 | 32.0 | stopped at ~11 min, best 18 (96k evals), stuck from t = 30 s |

Seeds 12 and 13 of pgl 19 × Z169 started in the two freed cores (same settings, 3600 s).
