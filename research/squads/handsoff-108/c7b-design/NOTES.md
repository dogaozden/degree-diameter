# c7b-design: what the annealed hexagon lifts look like, and whether a formula can reach them (worker c7b, squad handsoff-108)

Folder: research/squads/handsoff-108/c7b-design/ (card: cards.md, "c7b-design"; reads c6-hexagon/NOTES.md and src/).
Nothing in c6's folder was written. Seeds used: 9100-9400 (random starts), 30000-31000 (q=3 sampling), 7000-7500,
108851+ only as the seed base of the matching-only runs (see runs/exp_hzero.sh). Light CPU throughout: one process at a
time, nice -n 10, q = 3, 4, 5 except one q = 7 build and three q = 7 evaluations (about 1 minute each).

## Bottom line (negative, with a quantitative reason)

- No formula family found. Every rule tested is at best as bad as random voltages, most are much worse (table below).
- The valid annealed lifts (q = 3 Z24, q = 4 Z20, q = 5 Z15) are statistically indistinguishable from random lifts:
  walk-sum counts are multinomial, apartment holonomies are uniform over Z_m, raw and normalised voltages are uniform,
  and nothing depends on point coordinates.
- A first-moment (Poisson) model predicts the cost of random lifts to 1-5 % at q = 4, 5, 7 and P(cost 0) at q = 3 to about
  30 % (m = 14-20). With it, the largest m at which random lifts are expected to exist is m* = 43 (q=3), 34 (q=4),
  30 (q=5), 29 (q=7). The table's 20, 20, 25, 30 are below m* except at q = 7, where the table's 30 is already above
  it (E/L = 1.21). The card's 31 at q = 7 is 2 above m*: any construction there must have anti-correlated walk sums.
- Annealing stops far below m*: q=3 reached 24 (m* 43), q=5 reached 15 (m* 30), q=7 reached 17 in c6 (m* 29).

## 1. The threshold model (src/thr.py)

Lift = H(q) + 2 matchings, Z_m, Delta = q+3, N = (q^6-1)/(q-1) points = lines. Cost = sum over point sources of uncovered
(line, g) pairs, as in hexeval. Non-backtracking walks of odd length <= 7 from a point: W = sum_{k=1,3,5,7} Delta(Delta-1)^(k-1);
n = W/N walks per (point, line) pair.
- E(m) = N^2 m exp(-n/m): expected uncovered triples for a random lift.
- L(m) = 2 ln N! + (2N + (q+1)N) ln m: log of the number of lift tuples (sigma_1, sigma_2, mv_1, mv_2, hv).
- Heuristic threshold m* = largest m with L >= E (expected number of valid lifts >= 1). Poisson/independence assumption;
  Janson-type correlation corrections could move it by up to about Delta/2 in log scale (not computed).

| q | N | Delta | walks/pair n | m* (heuristic) | table m | E/L at table m | E/L at m* | E/L at m*+1 |
|---|---|---|---|---|---|---|---|---|
| 3 | 364 | 6 | 268.3 | 43 | 20 | 0.0004 | 0.94 | 1.11 |
| 4 | 1365 | 7 | 246.1 | 34 | 20 | 0.0037 | 0.90 | 1.13 |
| 5 | 3906 | 8 | 246.0 | 30 | 25 | 0.13 | 0.77 | 1.03 (m=31) |
| 7 | 19608 | 10 | 274.4 | 29 | 30 | 1.21 (m=30) | 0.86 | 1.21 (m=30); 1.67 at m=31 |

## 2. Calibration: random lifts (full hexagon voltages, hexeval point cost, ITERS=0)

| q | m | observed point cost (seeds) | predicted E | source |
|---|---|---|---|---|
| 3 | 20 | P(0) = 0.027 (1000 samples) | e^-E = 0.019 | runs/p0_q3.tsv |
| 3 | 19 | P(0) = 0.141 (1000 samples) | e^-E = 0.156 | runs/p0_q3.tsv |
| 3 | 16 | P(0) = 0.93 (150) | 0.90 | runs/p0_q3.tsv |
| 4 | 20 | 172, 140, 150 | 169 | runs/scan2_q4.tsv |
| 4 | 24 | 1465, 1436, 1480 | 1575 | runs/scan2_q4.tsv |
| 4 | 32 | 27098, 26655, 26852 | 27250 | runs/scan2_q4.tsv |
| 5 | 15 | 16, 10 | ~17 | runs/scan2_q5.tsv |
| 5 | 24 | 12612, 12616 | 12960 | runs/scan2_q5.tsv |
| 5 | 30 | 123223, 123886 | 125800 | runs/scan2_q5.tsv |
| 7 | 28 | 592516 | 596500 | runs/scan2_q7.tsv |
| 7 | 30 | 1222240 (1 dup) | 1228000 | runs/scan2_q7.tsv |
| 7 | 31 | 1694368 (1 dup) | 1705000 | runs/scan2_q7.tsv |

Note: the first scan of q=3 read the dup count instead of the cost (fixed; those numbers are discarded).

## 3. Structure of the valid lifts (src/holo.py, src/wcount.c, src/structan.py)

- Raw voltages (gauge dependent, q=5 Z15 valid, sols/q5_m15_hx2.sol): hexagon histogram over Z_15 between 1456 and 1630
  per value (mean 1562), matching histogram 497-547 (mean 521). Uniform.
- Switching normal form (BFS tree of H(5) switched to 0; 15,625 cotree voltages): histogram 1016-1064 per value. Uniform,
  so the hexagon part cannot be switched to a few values.
- Apartment holonomies (sum of hexagon voltages around 12-cycles, gauge invariant): fraction zero 0.038 (q=3 Z24;
  uniform 1/24 = 0.042), 0.052 (q=4 Z20; 0.050), 0.069 (q=5 Z15; 0.067). Matching-cycle holonomies are uniform too.
- Walk-sum multiplicities (nb walks of odd length <= 7 per (point, line) pair, dispersion = Var_g / Mean_g):
  valid q=3 Z24 0.938; valid q=4 Z20 0.948; valid q=5 Z15 0.934; random q=5 Z15 0.932. Multinomial value 1 - 1/m:
  0.958, 0.950, 0.933. So valid lifts have exactly the walk-sum statistics of random lifts (no balancing).
- Trivial hexagon voltages (matchings only, runs/hz_q3_m20.sol, hz_q3_m24.sol): dispersion 1.31 and 1.22. Walks with the same
  matching sequence collide, so walk sums clump. Random trivial lifts cost 1.5-2x more than full random lifts at the same m
  (q=3, m=28: 435-494 against 230-255). Hexagon voltages are what decorrelates the walk sums.
- Coordinates: mutual information between a raw hexagon voltage and each of the 7 coordinates of its point is at the
  sampling-bias level (0.0002-0.0014 nats against bias 0.0012), q=5 valid lift. No dependence.
- Matching-only annealing, q=3 (runs/exp_hzero.sh, HZERO=1): Z12, Z16, Z20, Z24 valid (Z24 in 3479 steps); Z28 best 28
  after 8000 steps; the full-hexagon annealer also stops at Z24 (c6) with Z28 at cost 12 (c6 notes).
- Switching fact: any hexagon voltage of the form f(p) + g(l) is switching-trivial (it equals zero on hexagon edges with
  altered matchings). A formula can only matter through flag-dependent voltages.
- Not done: symmetry under Aut(H(q)) (needs G2(q) generators; not computed).

## 4. Formula families tested (all negative)

- Constant matching voltages (mv_1 = a, mv_2 = b on all points, hexagon 0, random matchings; all (a,b), src/fam.py constscan):
  best point costs 11 (m=16), 586 (m=20), 20007 (m=24). Random lifts give 0-3, 1-4, about 45 at the same m. Dead.
- Families at q=3, m=24 (150 samples each, src/fam2.py; cost includes the dup penalty, medians shown):
  random 46 (min 28); hexagon voltages in {0, 12} (Z_2 gain) 78 (min 47); bilinear hexagon voltage
  B(x_p, x_idx(l)) * c mod m 58 (min 32). All worse than random.
- q=3, m=20 (120 samples): random median 6 (zero 0 of 120), index-linear matchings + random hexagon 7 (one zero, min 0),
  two-valued hexagon voltages {0, c} 7, bilinear 7. No family beats random.
- q=5, m=16 (60 samples each): see the table appended below (runs/fam2_q5_m16.txt).

## 5. What this means for the cell (10,8)

- Random-like constructions (any family whose walk sums behave like independent uniform values) cannot reach m = 30 at
  q = 7 (E/L = 1.21) and cannot reach 31 (E/L = 1.67). The table's 30 must have anti-correlated walk sums, i.e. a
  structure, not luck. Its existence is consistent with the model only if the construction is far from random.
- A testable mark of such a construction: zero uncovered triples AND walk-sum dispersion clearly below 1 - 1/m
  (src/wcount.c prints it). Random survivors give 1 - 1/m; annealed lifts give the same.
- Do not spend CPU on annealing or random sampling at Delta = 10 for m >= 29 (expected count of random valid lifts is
  e^(-2e5) at m = 30).

## Next (not done)

- Find the automorphisms of H(q) (q = 3 first) and test lifts invariant under a semiregular subgroup K on points: the
  constraints then come in K-orbits and annealing searches orbit values only. This is the one route that changes the
  search space rather than the cost function (the first moment is unchanged, as the orbit count scales as 1/|K| in both
  terms).
- Check the Janson correction for the first moment at q = 3 with E in 4-40 (sampling P(0) at m = 21-24 needs about
  10^5 samples: too slow with hexeval; a C sampler would do it).

## Files

- src/hexgen2 (H(7) built: hex/hex_q7.bin), src/hexeval (c6 copy, unchanged), src/indep, src/lift3, src/hexcheck (copies).
- src/wcount.c: non-backtracking walk-count multiplicities and the uncovered count (validated: equal to hexeval's cost
  on random lifts, 47 = 47, and 0 on the valid lift). src/holo.py: apartment and matching-cycle holonomies.
  src/structan.py: raw and normalised voltage histograms, mutual information. src/thr.py: first-moment thresholds.
  src/fam.py, src/fam2.py: formula-family writers and evaluators (through hexeval, IN= file, ITERS=0).
- runs/: exp_hzero.sh (matching-only annealing), scan2.sh (random-start costs, q=4,5,7), p0_q3.sh (P(0) at q=3),
  logs hz_q3_m*.log, hz_summary_q3.txt, scan2_q*.tsv, p0_q3.tsv, constscan_q3.txt, fam2_q5_m16.txt.
- sols/: copies of c6's valid lifts (q3_m24_hx, q4_m20_hx2, q5_m14_fix, q5_m15_hx2, q3_cyc22_a).
