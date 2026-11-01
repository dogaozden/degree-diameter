# Round 3 cards (raise-small-d, 2026-11-02)

Common: read research/squads/raise-small/HEADER.md first (rules, tools). Values to beat now:
(3,11) 1,474 · (3,12) 2,436 · (3,13) 4,324 · (3,14) 7,008 · (3,10) 810 · (4,12) 74,066 · (4,13) 192,382.

## What rounds 1-2 found (do not repeat)

- Joint base+voltage annealing (bin/salift_s) over metacyclic groups Z_m x|_r Z_k with SMALL bases is the method.
  2+2 bases (p = 2, n = 4N) won D = 12 and D = 13: (3,12) 2,436 = Z29 x|_7 Z21 (N = 609, director scan, 2+2), (3,13)
  4,324 = Z47 x|_2 Z23 (N = 1,081, card r2/d02, first 22-s screen). At D = 14, 3+3 (7,008 = Z73 x|_10 Z16, N = 1,168,
  r2/d03 chaining a cost-2 state) and 2+2 (7,004 = Z103 x|_8 Z17, N = 1,751, r2/d04) are level.
- Near misses: (3,13) 2+2 Z55 x|_2 Z20 (N = 1,100, n = 4,400) cost 2 [r2/d02 folder]; (3,14) 2+2 Z37 x|_8 Z48 (N = 1,776,
  n = 7,104) cost 2 [r2/d04 folder]; (3,14) 3+3 Z98 x|_19 Z12 (N = 1,176) cost 4 [director, runs/A3]; (3,12) 2+2
  Z43 x|_4 Z14 (N = 602) cost 4 [director, runs/D12p2]; (3,11) 4+4 Z48 x|_5 Z4 (N = 192, n = 1,536) cost 2 but an exact
  2-move local minimum.
- Groups: large k and large r-order d (Frobenius-like, m prime, d = k) solve fastest; k = 6 groups are nearly abelian
  (costs 30-130). Non-metacyclic groups were not better. Bases with p >= 5 are worse (costs 6-60). Orbit-constrained
  lifts (voltages equivariant under a base rotation and a group automorphism of order 3) were much worse (cost 60).
- A chain link that restarts at T0 = 10 usually loses the state; for cost <= 4 states use T0 = 4 and short links.
- Δ = 4: quartic joint lifts (salift4/salift4m) stayed at cost 18 (4,9), 30 (4,10), 36 (4,11): not competitive with
  Haar at this CPU. Haar (hmeta): (4,14) raised to 498,798 (r1/c15, Z3079 x|_568 Z81, a fresh seed after cost 1); near
  misses (4,12) Z2861 x|_1385 Z13 cost 2 (n = 74,386), (4,13) Z3851 x|_498 Z25 and Z1163 x|_102 Z83 cost 4, (4,11)
  Z1171 x|_166 Z13 cost 6.
- Director scans running now (do not repeat): 2+2 at D = 13 over N = 1,101-1,300 (k >= 12, ascending); 2+2 at D = 12
  over N = 593-720; 3+3 at D = 14 over N = 1,171-1,300 (k >= 12).

## Cards

- **e01 (3,13) 2+2, chain and fill.** Chain r2/d02's cost-2 state at N = 1,100 (Z55 x|_2 Z20; find the .best with
  header "1100 1 2 2" in research/squads/raise-small/r2/d02/), T0 = 4, many short links with new seeds; then screen
  groups of order 1,082-1,100 that d02 did not try.
- **e02 (3,13) 2+2, high band N = 1,301-1,420** (n = 5,204-5,680). Screens (k >= 12, d large), chain the best.
- **e04 (3,12) 2+2, band N = 721-820** (n = 2,884-3,280).
- **e05 (3,12) 3+3 at D = 12, N = 407-480** (n = 6N > 2,436; 3+3 is untested at D = 12).
- **e06 (3,14) 2+2: chain r2/d04's cost-2 state at N = 1,776 (Z37 x|_8 Z48)**, then screen 1,753-1,800 groups d04 did
  not try (d04 tried Z103 x|_8 Z17 solved, Z59 x|_3 Z29, Z43 x|_3 Z42, Z61 x|_4 Z30, Z127 x|_63 Z14, Z113 x|_35 Z16).
- **e07 (3,14) 3+3 band N = 1,301-1,400** (n = 7,806-8,400) and 2+2 band N = 1,801-1,900.
- **e10 Δ = 4 Haar chases (hmeta).** (4,12): fresh seeds on Z2861 x|_1385 Z13 and 3-4 other groups of order
  37,034-37,400; (4,13): fresh seeds on Z1163 x|_102 Z83 and Z3851 x|_498 Z25 and two new Frobenius groups of order
  96,192-97,000 (odd order at odd D). Fresh seeds beat long chains in round 1.
- **e11 (3,10) beat 810 (2013-table cell, our 810).** 3+3 (N = 136-150) and 4+4 (N = 102-112) joint annealing over
  metacyclic groups and Z_c products with k >= 4, many seeds, then the exact polisher bin/polish on every state with
  cost <= 4 (fast at N < 150). The own-small job found 816/820 at cost 4 (exact local minima) with SmallGroups; 2+2
  lifts at D = 10 are ruled out exhaustively (orders 200-250).
