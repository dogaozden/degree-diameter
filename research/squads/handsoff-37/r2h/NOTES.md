# r2h: n = 169 (non-cubic case), worker notes

Start: 2026-10-31 17:36:32Z (date -u). Stop about 19:36-19:50Z (2 h to 2 h 15).

## Setup (from card r2h)
- Sides A = 85, B = 84. x in A with degree 2 has a perfect radius-6 tree (1+2+4+8+16+32+64): depth 0..5 full,
  64 leaves at depth 6 (A), 42 outer B at depth 7. Only free choice: wiring of leaves to outer B vertices
  (outer B deg 3, leaves deg 2, two leaves deg 1 = the other degree-2 A vertices).
- Plan: C tabu over this wiring (2-switches + leaf shifts), bit-parallel 7-step closure for far (~5 us).
  Calibrate on the analogue R = 4 (D = 5, n = 41).

## 17:48Z: first code and numbers
- tabu169.c: tabu over the full leaf-outer wiring (2-switches + leaf shifts, full neighbourhood ~7.9k moves, ~50 ms per
  iteration). Cost = far (pairs at distance > 7, bit-parallel 7-step closure, ~6 us per evaluation).
  Calibration: R = 4 (D = 5, n = 41): far 0 at the random start (apsp VALID, diam 6); the analogue is easy.
  Note: the leaf wiring has 2 deficit leaves (H-degree 1) and 42 outer vertices of degree 3 (E = 126 H-edges).
- n = 169, 60 s, seed 1: init far 1552 -> best 185; seed 7: best 168 after 60 s (still falling).
- tabu169s.c: same search restricted to an involution t of the tree (MASK bit 0 set: flips the root branches, fixes only
  x) and sigma = (2k, 2k+1) on the outer vertices (WLOG, all outer orbits free). Orbit moves (2 patterns per pair of
  reps, leaf shifts to {d, td}). ~34 ms per iteration. MASK = 1, 30 s: best 207 (not yet compared at equal time).
- A 500 s run of tabu169 (seed 11) is in the background (output out/n169_base_s11.edges is written on each new best).

## 17:59Z: results so far (n = 169, cost = far)
- tabu169 (no symmetry), 500 s, seed 11: best 169 (out/n169_base_s11.edges). 60 s seed 7: 168 (best169 before the sym run).
  Far pairs of the 169 best: 57 leaf-leaf, 32+12 depth5-outer / depth5-depth5 (B-B), 24 depth4-leaf, 22 outer-outer.
  Degrees: 3 A-vertices of degree 2 (x plus two leaves), all others 3, as predicted by the counting argument.
- tabu169s (involution MASK = 1: root branches swapped, t fixes only x; outer sigma = (2k, 2k+1)), 500 s, seed 1:
  best 144 (out/sym_m1_s1.edges, copied to best169.edges, scored far 144, diam 9). 22984 iterations, ~22 ms each.
  Symmetric search beats the unrestricted one at equal time (144 vs 169).
- Next: other tree involutions (MASK = 3, 5, 9, 17, 33, 63), then tenure / longer runs for the best MASK.
