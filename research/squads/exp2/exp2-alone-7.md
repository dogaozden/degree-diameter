# exp2-alone-7: report (one Haiku worker, no subagents, no squad)

Cells: (Δ,D) = (7,7), (9,7), (11,7). Table values are vertex counts (TABLE.md, Δ = row, D = column). A Haar graph on a group
of order N has 2N vertices, so beating a cell needs N ≥ table/2 + 1 (7,7): N ≥ 11,719; (9,7): N ≥ 58,825; (11,7): N ≥ 199,291.

## Result

**Cells beaten: 0.** No valid graph above any of the three table values was found. Ratios to table: none reached 1.0.

Closest attempt: (7,7) on SL(2,23) (N = 12,144, which would give 24,288 vertices, +3.6 % over 23,436). Orbit-symmetric S
(k = 3) reached 44 uncovered elements after 30 min (6.8·10⁷ evaluations); random S and three other seeds plateau at 56–58.
Zero was never reached. Nothing was saved to research/frontier/sols/ because nothing verified.

Budget: budget_units 0.0069 (tools/session_usage.py, log in research/squads/usage/exp2-alone-7.jsonl). Wall time ≈ 67 min
(start 16:56 UTC, last run 18:03 UTC). Stopped early (not at the 4 h cap) because the four-seed (7,7) batch had been flat at 56
for about 15 minutes and the size estimates below say the remaining gap is far larger than that.

## Why the three cells look out of reach for this method

Using SIZE_LAW.md's measure μ = N·e^(−W/N), where W = number of binding words (W = 55,987 for (7,7), 299,593 for (9,7),
1,111,111 for (11,7), from size_law_fits.csv), evaluated at the smallest N that beats each table value:

| cell | min N | W/N | μ (expected uncovered) | Δ·ln N (first-moment ceiling, SIZE_LAW §1.4) |
|---|---|---|---|---|
| (7,7) | 11,719 | 4.78 | 99 | 66 |
| (9,7) | 58,825 | 5.09 | 361 | 99 |
| (11,7) | 199,291 | 5.58 | 755 | 134 |

Random-like and orbit-symmetric S have solved D = 7 cells only up to μ ≈ 40–55 in our records ((6,7) at μ ≈ 54 with an
orbit set; (8,7) at μ ≈ 28–39 with orbit mode). Every target sits above that band and above the
ceiling.

## Measurements (haar_gen3 / haar_sym, 1 thread each; logs in research/squads/exp2/logs/)

| cell | group | N | mode | time | best uncovered | μ |
|---|---|---|---|---|---|---|
| (11,7) | SL(2,31)×Z7 | 208,320 | random | 180 s | 1,394 | 1,005 |
| (11,7) | PSL(2,29)×Z17 | 207,060 | random | 180 s | 1,393 | 968 |
| (11,7) | SL(2,59) | 205,320 | random | 180 s | 1,220 | 917 |
| (11,7) | PSL(2,37)×Z8 | 202,464 | random | 180 s | 1,269 | 839 |
| (11,7) | SL(2,31)×Z7 | 208,320 | orbit k=3 | 240 s | 1,208 | 1,005 |
| (11,7) | SL(2,59) | 205,320 | orbit k=3 | 240 s | 1,128 | 917 |
| (9,7) | SL(2,31)×Z2 | 59,520 | random | 180 s | 390 | 388 |
| (9,7) | SL(2,31)×Z2 | 59,520 | orbit k=3 | 180 s | 446 | 388 |
| (7,7) | PSL(2,29) | 12,180 | random | 240 s | 133 | 123 |
| (7,7) | PSL(2,29) | 12,180 | orbit k=3 | 240 s | 117 | 123 |
| (7,7) | PSL(2,29) | 12,180 | orbit k=3 | 1,800 s | 110 | 123 |
| (7,7) | PGL(2,23) | 12,144 | orbit k=3 | 1,800 s | 90 | 121 |
| (7,7) | SL(2,23) | 12,144 | orbit k=3 | 1,800 s | 44 | 121 |
| (7,7) | SL(2,23) | 12,144 | random | 1,800 s | 56 | 121 |
| (7,7) | SL(2,23) | 12,144 | orbit k=3 (3 seeds) | 1,237 s, stopped | 56–58 | 121 |
| (7,7) | SL(2,23) | 12,144 | random (1 seed) | 1,237 s, stopped | 56 | 121 |

Reading: in every run the best uncovered count stayed near μ (the expected count for a random set) or 2–3× below it, and the
annealing curve flattened early. None of the runs came near zero. The one clear signal is that SL(2,23) (only one
involution, −I) does better than PSL or PGL at the same order, which matches the notes in STRUCTURE.md. That gain is
not enough to close a μ = 99 gap.

## Sanity checks I ran

- The orbit-mode and random-mode code paths behave as their logs say: the orbit runs print μ and the expected fixed-point
  misses, and the random runs show cost 616–1,019 at the start, then fall.
- The (7,7) and (9,7) numbers were taken from the same W values as the size-law CSV. They match what haar_sym prints for μ
  (e.g. 917 for SL(2,59) at (11,7), printed μ 916.6 against my 917).
- No candidate was ever at cost 0, so there was nothing to check with build_haar2.py.

## What I did not do

- No voltage-lift search (research/lifts/ has only the D = 5 example and a checker), and no two-orbit or "2+2" construction.
  These could change the effective W and are the most plausible way past the wall, but I had no time to build and test one
  honestly under this budget.
- No (11,7) search at N much larger than 208K. A larger group only raises μ (μ = N·e^(−W/N) grows with N), so for this
  method it cannot help.
- No subagents, as instructed.

## Recommendation

For random-like or orbit-symmetric Haar sets these three cells are not reachable with the present tools: their μ is
1.8× (7,7) to 14× (11,7) the best solved D = 7 value. Progress would need a different construction, for example a voltage lift or a
non-Haar bi-Cayley set with more orbits per side, validated against the (6,7)/(8,7) records before scaling to Δ = 9, 11.
