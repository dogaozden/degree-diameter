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

## 19:06Z: full results table (n = 169, far = pairs at distance > 7, all graphs scored by bin/score37)
Model (fixed by the card's counting argument): root x (A, degree 2) with a full binary tree to depth 6, 64 leaves (A),
42 outer B vertices (distance 7), wiring H = 126 leaf-outer edges (leaves H-degree 2, two leaves H-degree 1, outer 3).
Cost evaluated by a bit-parallel 7-step closure (~5 us per graph). Tabu over 2-switches + leaf shifts (full neighbourhood).

| run | search | time | far | file |
|---|---|---|---|---|
| tabu169 seed 1 | no symmetry, tenure 10-30 | 60 s | 185 | out/n169_test.edges |
| tabu169 seed 7 | no symmetry | 60 s | 168 | out/n169_test2.edges (= best169_far168.edges) |
| tabu169 seed 11 | no symmetry | 500 s | 169 | out/n169_base_s11.edges |
| tabu169s MASK 1 seed 1 | involution swapping the root branches | 500 s | **144** | best169_far144.edges (also out/sym_m1_s1.edges) |
| tabu169s MASK 63 seed 1 | complement involution | 500 s | 144 | out/sym_m63_s1.edges (distance profile identical to MASK 1) |
| tabu169s MASK 1 seed 2 | same | 300 s | 175 | out/sym_m1_s2.edges |
| tabu169s MASK 1 seed 3, tenure 5-12 | same | 300 s | 159 | out/sym_m1_s3_t5_12.edges (stalled after 85 s) |
| tabu169s MASK 1 seed 3, tenure 30-60 | same | 300 s | 186 | out/sym_m1_s3_t30_60.edges (stalled after 22 s) |
| tabu169s MASK 1 seed 4 | same | 150 s | 157 | out/sym_m1_s4.edges |
| tabu169s MASK 1 seed 5 | same | 150 s | 191 | out/sym_m1_s5.edges |
| tabu169s MASK 1, restart every 800 | same | 300 s | 161 | out/sym_m1_s1_p800.edges |
| tabu169s MASK 2 (depth-1 vertices fixed) | fixed B vertices | 300 s | 170 | out/sym_m2_s1.edges |
| tabu169s MASK 8 | fixed depth <3 | 300 s | 161 | out/sym_m8_s1.edges |
| tabu169s MASK 16 | fixed depth <4 | 300 s | 162 | out/sym_m16_s1.edges |
| tabu169w (cost = far7 + far9, tie-break) MASK 1 seed 1 | weighted cost | 300 s | 167 | out/w_m1_s1.edges |
| tabu169c: from 144 graph, symmetric moves, seed 7 | continuation | 300 s | 144 (no gain) | out/cont144_s7.edges |
| tabu169i: from 144 graph, full neighbourhood, seed 8 | continuation, unrestricted | 300 s | 144 (no gain) | out/full_from144_s8.edges |

Findings:
- The involution MASK 1 (root branches swapped; sigma pairs the outer vertices; all leaves in free orbits) is the best
  symmetry type tried. Masks with bit 0 set are conjugate (identical init fingerprint and the same distance profile);
  masks that fix depth-1 vertices (2, 8, 16) are worse at 300 s.
- Tenure 10-30 is best of the three tried; 5-12 stalls, 30-60 stalls early. Far is not a smooth cost: seeds spread
  144 to 191 at 150-500 s. Runs converge in about 250 s.
- The 144 graph is a local minimum for both the symmetric and the full 2-switch neighbourhood (300 s each, no gain).
- Not run (time): order-3 quotient with s permuting {x, y, z} (card's first symmetry option; needs the tree not to be
  rooted at a fixed vertex, so this is a different encoding), SA instead of tabu, exact completion of the leaf wiring.

Best n = 169 candidate: far 144 (not a candidate; far > 0). Not run through apsp (far > 0 so no claim).
Reproduce: r2h/tabu169s (source tabu169s.c): `./tabu169s 6 1 500 1 out.edges` (MASK 1, seed 1, tenure 10-30, pert 3000;
note that the run is time-limited, so the trajectory depends on the speed of the machine).

## Process notes
- Monitor-based waiting: a `pgrep -f` loop matches its own command line and never exits; I stopped those and waited with
  `tail --pid` or `kill -0` instead.
- Each run was a foreground command with an explicit Bash timeout of 600000 ms (300-500 s runs completed normally).

## 19:30Z: last runs
- tabu169s MASK 1 from scratch, 200 s: seed 8 far 169, seed 9 far 169; 250 s: seed 10 far 178 (stalled after 22 s),
  seed 11 far 162. So over seeds 1-11 for MASK 1: 144, 175, 157, 191, 159, 186 (tenure variants), 169, 169, 178, 162.
- tabu169c (continuation from the far-144 state, symmetric moves): 2-switch kicks (300 s, seed 7): 144, no gain;
  8-switch kicks every 500 iterations (250 s, seed 12, 19 restarts): 144, no gain.
- Conclusion: best n = 169 far is 144 (out/sym_m1_s1.edges = best169_far144.edges). Far 0 is not reached: the wiring
  search is rugged (large seed variance, early stalls) and the best symmetric local minimum is still far from 0.
  Next steps if continued: (1) population / path relinking between the 144 and other good symmetric states;
  (2) an exact or SAT completion of the leaf wiring for the last ~50 bad pairs; (3) the order-3 encoding of card step 2.
- tabu169s MASK 1 seed 13, 200 s: far 168 (out/sym_m1_s13.edges). Best stays 144 (best169_far144.edges). Stopped 19:37Z (2 h 0 min of work).
