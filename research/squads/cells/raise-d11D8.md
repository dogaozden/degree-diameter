# raise-d11D8: beat 2,258,520 at (Δ, D) = (11, 8)

Job "raise-11-8" (Haiku worker, cloud session, started 2026-10-25 ~07:55 UTC; budget 6 h, until ~14:00 UTC).
Record to beat: 2,258,520 = 2·|PSL(2,59) × Z_11| (N = 1,129,260), file `research/frontier/sols/d11D8_psl_59_11_orb5_ORBW5_s3.txt`,
k = 5 orbit method (`research/structured/`, STRUCTURE.md §8). Table value 2,246,940.

## Method
- Orbit annealing, `research/structured/haar_sym`, `ORBIT="5 2 1" ORBW=5 K=8 THREADS=1`: S = {e} ∪ two α-orbits of size 5,
  α = conjugation by an order-5 element × (z ↦ r z on Z_n). Only groups with every prime of n ≡ 1 mod 5 (so Fix(α) = C_Q(g) × 0).
- Candidate groups: `research/structured/tools/orb_screen.py 11 8 1129260 1200000 "5 2 1" --samples 400 --nmax 2000`
  (random symmetric S statistics: fix, min, p1, p10, median). Output in scratchpad (screen_k5.txt).
- Any N > 1,129,260 with a VALID check is a new record (2N > 2,258,520).

## Log
- 07:59 UTC: screen running. Baseline psl 59×11 random sample: fix 29, min 19, p1 28, p10 53.
  Started psl 19 × Z331 (N = 1,132,020, μ = 61.8, fix 9), ORBW=5, 2 seeds, 7200 s each.
- 08:03 UTC: screen done (60 candidates, `orb_screen.py ... --samples 400`; ranking by (p1+p10)/2 of random symmetric S cost).
  Baseline psl 59×11: min 19, p1 28, p10 53. Best near-record alternatives: psl 19×Z331 (N 1,132,020, fix 9: min 37, p1 47),
  sl 16×Z281 (N 1,146,480, fix 14: min 52, p1 71; SL(2,16) has no cyclic subgroup of order ≥ 64, so no wide rows).
  Everything with a cyclic factor of order ≥ 340 or with fix in the thousands is out (min ≥ 70–1,000,000).
  Running (ORBIT="5 2 1" ORBW=5 K=8 THREADS=1, 7200 s each): psl 19×Z331 seeds 1,2; sl 16×Z281 seeds 1,2.
