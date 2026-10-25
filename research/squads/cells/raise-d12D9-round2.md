# Raise the (Δ,D) = (12,9) record, round 2 (Haar graphs)

Job "raise2-12-9", Haiku worker, branch `claude/raise-d12d9-bipartite-record-b26a5o`. Round 1 is on
`claude/raise-d12d9-bipartite-record-f510kc` (notes `research/squads/cells/raise-d12D9.md` there).

## Bar to beat (discrepancy)
- The brief says 34,026,720 (SL(2,41) × Z247, on master). Round 1's branch already has VERIFIED finds above it:
  **35,068,320** = 2·|SL(2,71) × Z49| (`research/frontier/sols/d12D9_sl_71_49_orb3f0_s2.txt`, checked by haarcheck_sl and
  haarcheck2). Not yet merged to master, so the coordinator may not have it recorded.
- So the bar used here is **N > 17,534,160** (2N > 35,068,320). Anything between 34,026,720 and 35,068,320 would be
  a record over master but not over round 1, and would not be worth the coordinator's time.

## Round 1 (what is NOT repeated here)
- k = 3, m = 4, f = 0 (ORBIT="3 4 0"), default ORBW (1), default COOL/REHEAT, seeds 1–5 (plus 1 of psl 73×91 seed 1–3),
  40–60 min each. Wins: psl 61×151, sl 97×19, psl 71×97 (seed 3), sl 71×49 (seed 2, 23k evals).
- Unsolved above the bar: sl 47×169 (μ 25.4, 5 seeds, best 6–10), psl 73×91 (μ 28.9, 3 seeds, best 6–11),
  sl 43×223 (best 12), sl 83×31 (best 8), sl 37×349 (best 36). pgl/GF(64)/sl 64 not run (no checker).

## Lever list for round 2 (all with the existing haar_sym, no code change)
1. **ORBW=3** (an uncovered α-fixed element weighs as much as an uncovered orbit). Never used in round 1; it helped
   at (11,8) (STRUCTURE §8). Expected fixed-point misses here ≈ 1.1 (sl 47×169) and ≈ 0.85 (psl 73×91).
2. **Longer runs** (2 h) with fresh seeds on the group closest above the bar (sl 47×169, μ 25.4).
3. **Group choice**: the only groups with N in (17,534,160, 17,700,000] and a checker are sl 47×169 (N 17,538,144),
   sl 37×349 (17,664,984), psl 73×91 (17,696,952). Next up: sl 43×223, sl 83×31 (≈ 17.72M, μ ≈ 29.5), psl 47×343
   (≈ 17.80M, μ ≈ 30). Larger N means larger μ (about +2 per 0.1M), so the smallest N above the bar is first choice.

## Checkers (built in scratchpad, same sources as the repo)
- SL(2,p)×Z_n above 20M vertices: `research/frontier/haarcheck_sl.c` and `research/frontier/haarcheck2.c` (both must pass).
- PSL(2,p)×Z_n above 20M vertices: `research/structured/tools/haarcheck_psl.c`.

## Runner
`haar_sym` built from `research/structured/haar_sym.c` (gcc -O3 -march=native -fopenmp). Each run:
`env ORBIT="3 4 0" ORBW=w THREADS=1 haar_sym 12 9 SECS SEED 8 OUT GROUP... n`. Logs: `research/structured/runs/d12D9r2_<tag>.log`.

## Log
### Batch 1 (started 15:03 UTC, 2 h each, 4 parallel)
- sl 47×169 ORBW=3 seed 6 and seed 7; sl 47×169 ORBW=1 seed 6 (control); psl 73×91 ORBW=3 seed 4.
(results appended below as they finish)
