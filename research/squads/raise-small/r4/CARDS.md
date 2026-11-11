# Round 4 cards (raise-small-d, 2026-11-02)

Common: read research/squads/raise-small/HEADER.md first (rules, tools). Values to beat now:
(3,12) 2,436 · (3,13) 4,324 · (3,14) 7,008 · (3,11) 1,474.

## What rounds 1-3 found (do not repeat)

- The method: bin/salift_s joint base+voltage annealing over metacyclic groups (tables from tools/gtab.py), small bases.
  Records: (3,12) 2,436 = 2+2 over Z29 x|_7 Z21 (N = 609); (3,13) 4,324 = 2+2 over Z47 x|_2 Z23 (N = 1,081);
  (3,14) 7,008 = 3+3 over Z73 x|_10 Z16 (N = 1,168), 7,004 = 2+2 over Z103 x|_8 Z17 (N = 1,751).
- Both 2+2 records came from the FIRST 15-25-s screen of their group; chains of stuck states rarely help, and many
  groups have a hard floor (every seed ends at the same cost: Z55 x|_2 Z20 at 2, Z93 x|_5 Z12 at 18, Z17 x|_4 Z8 at 2).
  So: many groups x 2-3 fresh seeds x short runs; chain only states at cost <= 4 that are not repeats of a floor.
- Thresholds: D = 13 2+2: cost 6 at N = 1,088 (Z17 x|_3 Z64, Z55 x|_3 Z20), 12-56 at 1,110-1,134, >= 80 above 1,300.
  D = 14 2+2: cost 2 at N = 1,776 (Z37 x|_8 Z48), 4 at 1,806 (Z43 x|_3 Z42), 10-22 at 1,808-1,830. D = 14 3+3: cost 4-8
  at 1,170-1,218, >= 54 above 1,300. D = 12 2+2: cost 4 at 602, 10-30 at 594-660, >= 28 above 720.
- Large r-order d (m prime, d = k: Frobenius groups) is the best predictor; k = 6 and small d fail. Odd order alone does
  not help (odd groups at D = 13 cost 12-28). Bases p >= 5, non-metacyclic groups, orbit constraints, targeted moves,
  tabu: no gain. Haar graphs (p = 1): exhaustive at D = 13 over odd orders >= 2,163 gives cost >= 52 (director sweep).
- Running now (do not repeat): director 2+2 scan D = 12 N = 660-720; e06 chains Z37 x|_8 Z48 at D = 14; D = 11 odd scans.

## Cards

- **f01 (3,13) 2+2, N = 1,082-1,120.** Every metacyclic group with r-order d >= 8 in that band (both parities;
  `glist.py 1082 1120 8 8`), 2 fresh seeds x 15 CPU-s each (T0 = 10); then 3 more seeds on the 3 lowest; chain <= 4.
- **f02 (3,13) 2+2, N = 1,121-1,170**, same plan.
- **f03 (3,14) 2+2, N = 1,753-1,800**, same plan except Z37 x|_8 Z48 (e06 has it) and Z103 x|_8 Z17 (solved).
- **f04 (3,14) 2+2, N = 1,801-1,850**; also chain round 3 card e07's cost-4 state for Z43 x|_3 Z42 (N = 1,806;
  research/squads/raise-small/r3/e07/, the .best with header "1806 1 2 4").
- **f05 (3,14) 3+3, N = 1,169-1,215**, every group with d >= 6 and k >= 8, 2 fresh seeds x 20 CPU-s.
- **f06 (3,12) 2+2, N = 593-660, second pass**: 3 NEW seeds (seeds 5, 6, 7) on every group with d >= 6 from
  `glist.py 593 660 6 6` (the director's scan used seeds 1, 2 only), 15 CPU-s each.
