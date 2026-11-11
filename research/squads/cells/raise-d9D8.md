# Cell (Δ, D) = (9, 8): raise-9-8 job, round 2 (Haiku worker)

Branch `claude/raise-d9d8-haar-round2-q5t083`. Brief: beat our (9,8) record, 540,360 vertices (N = |G| = 270,180,
psl 19 × Z79, orbit k = 3, m = 3, f = 0, found in 4.4·10⁵ evals at μ = 37.9). Table value 449,480; Moore bound 4,793,490.
Round 1 (branch `claude/raise-d9d8-haar-record-rqmcq3`, cells/raise-d9D8.md there) tried 12 orbit runs above the
record order, N = 270,312 to 277,860: none solved; best cost 1 (sl 16 × Z67, 1 h, two seeds).

## What round 2 checked (2026-10-25)

Candidate list from `research/structured/tools/orb_screen.py 9 8 270181 285000 "3 3 0" --list --nmax 2000`
(k = 3 needs every prime of n ≡ 1 mod 3). Random-S statistics = RANDORB, 150 samples, k = 3, f = 0:

| group | N | μ | |Fix| | min | p1 | p10 | median | round 1? |
|---|---|---|---|---|---|---|---|---|
| sl 16 × Z67 | 273,360 | 42.6 | 14 | 42 | 44 | 67 | 134 | yes (median 121) |
| sl 9 × Z379 | 272,880 | 41.8 | 17 | 106 | 126 | 216 | 687 | no |
| psl 9 × Z757 | 272,520 | 41.3 | 8 | 132 | 142 | 390 | 1136 | no |
| sl 8 × Z541 | 272,664 | 41.5 | 8 | 84 | 104 | 205 | 501 | no |

Reading: sl 16 × Z67 is the only group above the record with random-S statistics close to the record group's
(record, round 1: median 114 at μ 37.9). The other new candidates have small H and random medians 4–10× larger.
Groups with μ below 42 (psl 7 × Z1609, psl 9 × Z751, prod psl 3 × psl 3 × Z1879) have large cyclic factors and
random medians in the thousands (round 1). Not re-run.

Ruled out for this round, with reasons:
- Order-9 orbit, one orbit (ORBIT="9 1 0"): α³ acts trivially on H, so H × {0} consists of points with orbits of size 3.
  Their coverage behaves like λ/3, and |H|·e^(−λ/3) is 25–35 misses for H of order 500. Not run.
- Field automorphisms (Frobenius of order 3): already negative in STRUCTURE.md §5 (SL(2,8) × Z43).
- k = 5 or 7: no order-5/7 automorphisms with small fixed sets at this order (STRUCTURE.md §7).
- Heisenberg, AGL(1,p), metacyclic scalings: negative in STRUCTURE.md §5.

## Runs (round 2)

Four `haar_sym` runs of sl 16 × Z67, `ORBIT="3 3 0"`, THREADS=1, 9000 s each, logs in `research/structured/runs/raise_d9D8_r2/`:

| seed | settings | status |
|---|---|---|
| 21 | default | running (started 15:00 UTC) |
| 22 | default | running |
| 23 | RESTART=1 | running |
| 24 | COOL=60 REHEAT=300 | running |

## Notes for a resumed session

- Solutions are written to `research/structured/runs/raise_d9D8_r2/d9D8_sl_16_67_orb3f0_r2s<seed>.txt` only when cost 0.
  Verify with `research/frontier/build_haar2.py` (N ≤ 10M), then move to `research/frontier/sols/` as `d9D8_*`.
- Check a run with `grep RESULT research/structured/runs/raise_d9D8_r2/*.log`.
- The binary is `research/structured/haar_sym` (gcc -O3 -march=native -fopenmp; gitignored, rebuild if missing).

## Result (2026-10-25, about 2 h in): three solutions above the record

Seeds 21, 23 and 24 (all sl 16 × Z67, k = 3, f = 0) reached cost 0 (haar_sym RESULT best=0):

| seed | settings | evals | time | vertices |
|---|---|---|---|---|
| 23 | RESTART=1 | 5.6·10⁶ | 944 s | 546,720 |
| 21 | default | 2.4·10⁷ | 3,959 s | 546,720 |
| 24 | COOL=60 REHEAT=300 | 3.8·10⁷ | 6,269 s | 546,720 |

Independent checks, both VALID, n = 546,720, 9-regular, diameter 8:
- `research/frontier/build_haar2.py` (eccA = eccB = 8, no duplicate edges; seeds 21, 23, 24)
- `research/frontier/check_haar_indep.py` (seed 23): eccA = eccB = 8, n = 546,720.
Saved to `research/frontier/sols/d9D8_sl_16_67_orb3f0_r2s{21,23,24}.txt`.
Edge-list sha256 for seed 23: ea5e39630486a45771975580532f3dc488b6c0f33a024fc16e547b6da3fe1def.
The Haar graph has a transitive group action on each side, so the two eccentricities from one vertex per side are the full diameter check.

This beats the 540,360 record by 1.2 % (+6,360 vertices). The coordinator must re-check the record independently before it is recorded.

Seed 22 (default) was still running at cost 1 at 7,320 s when this was written.

## Next rung: prod sl 5 × sl 5 × Z19 (N = 273,600, μ = 42.9), not solved

Three 5,400 s runs, `ORBIT="3 3 0"`, THREADS=1 (seeds 31 default, 32 RESTART=1, 33 COOL=60 REHEAT=300):
best costs 3, 1 and 3 after about 2.5·10⁷ evaluations each. |Fix(α)| = 35, expected fixed-point misses about 1.9.
Seed 22 (sl 16 × Z67, default, 9,000 s) also ended at cost 1 without a solution.

## Stopping point (2026-10-25, about 4 h in)

Next rungs above 273,360: prod sl 5 × sl 5 × Z19 (μ 42.9, stalled at cost 1–3 above), sl 13 × Z127 (μ 49, round 1 best 6),
and the groups with μ > 49 that round 1 screened. The record is now 546,720 vertices (sl 16 × Z67). The remaining rungs
are harder by μ and by fixed points, and the orbit method with k = 3, f = 0 has no cheap candidate left. Stopping here
rather than spending the rest of the budget on runs with a low chance. A new attempt would need a different group or
a different fixed-point treatment, not more seeds on this one.
