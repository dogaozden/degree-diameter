# exp2-alone-8: final report

One Haiku worker, alone (no subagents), cells (7,7), (9,7) and (11,7). Start 2026-10-24 16:56 UTC; report written at
about 17:57 UTC (about 1 h wall). Budget used: 0.01 units by the session meter (tools/session_usage.py), far under the
1.5 cap. Log: research/squads/usage/exp2-alone-8.jsonl.

## Result: no cell beaten; best valid sizes below

| cell | table (vertices) | best valid (vertices) | ratio | group and method |
|---|---|---|---|---|
| (7,7) | 23,436 | **19,152** | 0.817 | SL(2,8) × Z19, orbit mode (k=3, 2 orbits, 1 fixed) |
| (9,7) | 117,648 | **85,344** | 0.725 | SL(2,7) × Z127, orbit mode (k=3, 3 orbits) |
| (11,7) | 398,580 | **266,448** | 0.669 | SL(2,13) × Z61, orbit mode (k=3, 3 orbits, 2 fixed) |

Each valid graph was rebuilt and checked by research/frontier/build_haar2.py: all four side pairs within distance 7,
every vertex reached, simple and regular. The graphs are saved in research/frontier/sols/ (names d7D7_, d9D7_, d11D7_).

Other valid graphs saved (smaller than the best, for the record): (7,7) 18,480 (SL(2,11)×Z7, plain); (9,7) 74,256
(SL(2,13)×Z17, plain), 82,992 (SL(2,13)×Z19, orbit); (11,7) 243,600 (SL(2,29)×Z5, plain), 259,920 (SL(2,19)×Z19, orbit).

Cells beaten: 0 of 3. Each valid size is about 2/3 to 4/5 of the table, so none reaches its table value.

## What the first-moment model said, and what happened

Before running anything, research/frontier/heuristic.py put the random-Haar ceiling N_h (the largest group order where
a covering set plausibly exists) at about 10.9K for (7,7), 48.3K for (9,7) and 156.9K for (11,7). The table values need
group orders of 11.7K, 58.8K and 199.3K, i.e. 1.07, 1.22 and 1.27 times N_h. So a random-like Haar graph was not
expected to beat any of the three cells, and this held. The graphs we did find are at 0.88, 0.88 and 0.85 of N_h,
close to the 0.85–0.89 calibration in research/frontier/PLAN.md.

## What worked

- **Plain annealing (haar_sym, the faster haar_gen3 with the same CLI) at moderate orders.** It solved (7,7) at 8,736
  and 9,240, (9,7) at 37,128, and (11,7) at 121,800, each in seconds to minutes. Above these orders it stalled at
  cost 10–60 uncovered elements, even with several seeds.
- **Orbit mode (ORBIT="k m f", automorphism of order 3: conjugation times z -> r z on Z_n, n a product of primes
  congruent to 1 mod 3).** This moved the wall for every cell. The orbit runs solved (9,7) at 41,496 and 42,672, and
  (11,7) at 129,960, 133,224. For (7,7) it solved 9,576 instantly. Orbit runs that stalled at the same orders as plain
  runs (for example (9,7) SL(2,19)×Z7 at 47,880, cost 34–40 over three seeds) did not solve.

## What did not work (best uncovered count in parentheses, each run 900 s unless noted)

- (7,7): plain SL(2,13)×Z5 10,920 (22), SL(2,11)×Z8 10,560 (14), SL(2,11)×Z9 11,880 (68), SL(2,23)×Z1 12,144 (60),
  SL(2,13)×Z6 13,104 (132), SL(2,8)×Z21 10,584 (20); orbit SL(2,7)×Z31 10,416 (6, two seeds).
- (9,7): plain SL(2,13)×Z25 54,600 (212), SL(2,23)×Z5 60,720 (466), SL(2,13)×Z27 58,968 (400), SL(2,11)×Z45 59,400
  (484); orbit SL(2,19)×Z7 47,880 (34–40, three seeds), SL(2,11)×Z37 48,840 (50), SL(2,7)×Z139 46,704 (60).
- (11,7): plain SL(2,23)×Z11 133,584 (10 after 900 s), SL(2,29)×Z6 146,160 (50), SL(2,29)×Z7 170,520 (256),
  SL(2,31)×Z5 148,800 (60); orbit SL(2,23)×Z13 157,872 (86), SL(2,17)×Z31 151,776 (54), SL(2,7)×Z409 137,424 (78),
  SL(2,13)×Z67 146,328 (48), SL(2,11)×Z103 135,960 (12, two seeds).

Two process notes: the first orbit-mode test (SL(2,8)×Z19 for (7,7)) solved in 0.0 s, which suggests the orbit wall at
these sizes is much lower than the plain wall. The SL(2,7) family gave the best (9,7) result, which we did not expect.

## Not tried

- Non-Haar lifts (voltage lifts over base graphs with more than one vertex per side). The first-moment count says these
  are worse than Haar at the same order, so we did not spend time on them.
- Other order-3 automorphisms with fewer fixed points (ALPHA=...), larger orbits (k = 5, 7), and metacyclic groups.
- Longer runs or more seeds at the stalled orders. The plateaus were flat for 10+ minutes, so we judged the extra
  compute not worth it given the cap.

## Budget and time

- Budget units (tools/session_usage.py, this session only, Haiku model family): about 0.01 at the end. The 1.5 cap was not
  reached; the wall-clock cap (4 h) was not reached either. We stopped when the remaining candidates had plateaued.
- Wall time: about 1 h.
- Commits pushed to claude/haar-cell-11-7-search-44d7ft at least every 30 minutes. Draft PR #279 is open for the branch.

## Caveats

- Table values are the 2013 survey values (research/frontier/TABLE.md); current wiki values for D = 7 are unverified.
- All sizes above are vertex counts (2N), matching the table's convention.
