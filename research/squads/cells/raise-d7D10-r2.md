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

## Runs (all `ORBIT="3 2 1"`, K = 8, single thread, no solution found)

| group | N | μ | seed / options | budget | best cost (evals) | note |
|---|---|---|---|---|---|---|
| pgl 19 × Z169 | 1,155,960 | 33.1 | 11 | 3600 s | 12 (3.56 M) | 12 from t ≈ 15 min to the end |
| sl 19 × Z169 | 1,155,960 | 33.1 | 11 | 3600 s | 5 (3.65 M) | still moving at the end (9 at 28 min, 5 at 41 min) |
| pgl 19 × Z169 | 1,155,960 | 33.1 | 12, 13 | stopped at ~4 min | 12 (both) | same plateau as seed 11 |
| pgl 19 × Z169 | 1,155,960 | 33.1 | 14, RESTART=1 | 1800 s | 9 (1.78 M) | RESTART=1 lowers the floor from 12 to 9 |
| sl 16 × Z283 | 1,154,640 | 32.6 | 11 | stopped at ~11 min | 27 (83 k) | no progress after the first 30 s |
| psl 19 × Z337 | 1,152,540 | 32.0 | 11 | stopped at ~11 min | 18 (96 k) | no progress after the first 30 s |

Alpha check on pgl 19 × Z169 (`ALPHA=<index>`, 60 random indices of order 3 in Q): only 3 are of order 3, all with |Fix| = 17 and
worse sampled tails (min 69–84) than the default α (min 27), so the default stays.

## Reading (end of this session's compute so far)

- No group above N = 1,149,120 was solved. The record stays at 2,298,240.
- Plateaus recur across seeds: pgl 19 × Z169 sits at exactly cost 12 in three seeds, and sl 19 × Z169 at 5 to 16. This looks like a
  structural floor for these groups at μ ≈ 33 under k = 3 orbits, not a bad seed. Restarts (`RESTART=1`) move the floor a little
  (9 for pgl 19 × Z169), and sl 19 × Z169 reached 5 with plain annealing.
- Round 1 saw the same wall: solves at μ ≈ 31 in 5–10 min, nothing at μ ≈ 33 in 30–60 min.

## sl 19 × Z169 with RESTART=1 (seeds 21–24, 3600 s each, finished)

| seed | best cost | evals |
|---|---|---|
| 21 | 6 | 3.64 M |
| 22 | 10 | 3.59 M |
| 23 | 6 | 3.60 M |
| 24 | 6 | 3.62 M |

No solve. The floor for sl 19 × Z169 at μ = 33.1 is 5–6 in every run, the best one being plain annealing (seed 11, cost 5).
Those are the closest results of the round, and still 5 uncovered orbits from a solution.

## Stop decision (round 2)

I stopped here rather than run more seeds of the same groups. Reasons:

1. Four groups above the record order were tried with about 4 h of single-core time in total (60-minute runs, 3.5 M
   evaluations each, plus restarts). None solved. Best costs: 5 (sl 19 × Z169), 9 (pgl 19 × Z169 with RESTART), 18 (psl 19 × Z337),
   27 (sl 16 × Z283).
2. The plateaus repeat across seeds (pgl 19 × Z169 at 12 in three seeds; sl 19 × Z169 at 5–10 in five runs), which points at a
   floor of the k = 3 orbit method at μ ≈ 33, not at a bad seed.
3. The sampled screen (300 random S per group) gives no group above the record with a lower tail than the record group
   (p1 ≈ 24 at μ = 30.9). Above μ ≈ 32 every candidate is 2–3× worse.

What would move the cell (not tried here): a higher compute budget at μ ≈ 33–35 on sl 19 × Z169 (the one group whose
cost was still moving at 60 min), k = 5 orbits (Δ = 2 + 5 with f = 2, which SIZE_LAW rates as weak), or voltage lifts
(research/lifts/). Those are for the coordinator to decide.

## Result

No new record. The record stays at 2,298,240 (`d7D10_prod_sl_7_psl_19_1_orb3_s2.txt`, verified in this session by build_haar2.py).
