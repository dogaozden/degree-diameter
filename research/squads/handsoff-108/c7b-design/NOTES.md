# c7b-design: structure of the annealed hexagon lifts, the first-moment bar, and K-symmetric lifts (worker c7b)

Folder: research/squads/handsoff-108/c7b-design/ (card "c7b-design" in cards.md; reads c6-hexagon/NOTES.md and src/).
Nothing in c6's folder was written. Seeds: the matching-only runs used 108851+m (card range). The symmetric-search
runs used seeds 101-111, 20207, 3, 5, 11 and 21, which are outside the card range (none on the used list; a deviation
from the card's seed rule, noted here). Random-start calibration scans used hexeval seeds 7000-9500 and 30000-31000.
One heavy process at a time, nice -n 10, THREADS=1. python-igraph (BLISS) installed under c7b-design/pylib (local only).

## Bottom line

1. Formula families: none found. Every rule tried (constant matching voltages, two-valued or Z_2 hexagon voltages,
   bilinear, layer-based, index-linear) is at best random-like and most are much worse than random voltages.
2. The valid annealed lifts are statistically indistinguishable from random lifts (walk sums multinomial, apartment
   holonomies uniform, no dependence on coordinates). A first-moment (Poisson) model predicts random-start costs to
   1-5 % and P(cost 0) at q = 3 to within about 40 % (section 1). It puts the largest m with random lifts expected to exist at
   m* = 43 (q=3), 34 (q=4), 30 (q=5), 29 (q=7). At q=7 the table's 30 is already above it (E/L = 1.21), so a
   construction of 30 copies, and of the card's 31, must be structured, not random.
3. NEW, and the useful result: restricting the search to lifts invariant under a semiregular automorphism K of H(q)
   (cyclic of prime order P, acting fixed-point-freely on points and lines) and annealing on orbit variables works far
   better than unrestricted annealing (section 4). Verified valid lifts (explicit BFS, indep.c DIAMETER_OK):
   q=3 (Delta 6): 30 copies (21,840 vertices; table 20). q=4 (Delta 7): 20 copies (54,600; table 20, equal).
   q=5 (Delta 8): 20 copies (156,240; table 25; 21 reached cost 4 units, not valid). q=7 (Delta 10): 20 copies not
   reached in 2,500 steps (best 13 units = cost 559); table 30 is far off with this method (section 4.4).
   None of this is a record: the repo's current (6,8) record is 31,680 vertices (research/RESULTS.md, Oct 23 22:11 PT).

## 1. Threshold model (src/thr.py)

Lift = H(q) + 2 matchings over Z_m, Delta = q+3, N = (q^6-1)/(q-1). Cost = sum over point sources of uncovered (line, g)
pairs (hexeval). Non-backtracking walks of odd length <= 7 from a point: W = sum_{k=1,3,5,7} Delta(Delta-1)^(k-1); the
average number of walks per (point, line) pair is n = W/N.
- E(m) = N^2 m exp(-n/m): expected uncovered triples of a random lift.
- L(m) = 2 ln N! + (2N + (q+1)N) ln m: log of the number of lift tuples.
- m* = largest m with L >= E (expected number of valid lifts >= 1). Poisson/independence assumption; a Janson-type
  correction (positively correlated bad events) could move it, not computed.

| q | N | Delta | n | m* (heuristic) | table m | E/L at table m | E/L at m* | E/L at m*+1 |
|---|---|---|---|---|---|---|---|---|
| 3 | 364 | 6 | 268.3 | 43 | 20 | 0.0004 | 0.94 | 1.11 |
| 4 | 1365 | 7 | 246.1 | 34 | 20 | 0.0037 | 0.90 | 1.13 |
| 5 | 3906 | 8 | 246.0 | 30 | 25 | 0.13 | 0.77 | 1.03 (m=31) |
| 7 | 19608 | 10 | 274.4 | 29 | 30 | 1.21 (m=30) | 0.86 | 1.21 (m=30); 1.67 at m=31 |

Calibration of E against random starts (point cost, full random hexagon voltages, hexeval ITERS=0):

| q | m | observed | predicted E | source |
|---|---|---|---|---|
| 3 | 19 | P(0) = 0.141 (1000 samples) | e^-E = 0.156 | runs/p0_q3.tsv |
| 3 | 20 | P(0) = 0.027 (1000 samples) | e^-E = 0.019 | runs/p0_q3.tsv |
| 4 | 20 / 24 / 32 | 172,140,150 / 1465,1436,1480 / 27098,26655,26852 | 169 / 1575 / 27250 | runs/scan2_q4.tsv |
| 5 | 24 / 30 | 12612,12616 / 123223,123886 | 12960 / 125800 | runs/scan2_q5.tsv |
| 7 | 28 / 30 / 31 | 592516 / 1222240 / 1694368 | 596500 / 1228000 / 1705000 | runs/scan2_q7.tsv |

## 2. Structure of the valid unrestricted lifts (src/holo.py, src/wcount.c, src/structan.py)

- Raw voltages (gauge dependent), q=5 Z15 valid: hexagon histogram over Z_15 between 1456 and 1630 per value, matching
  497-547 per value. Uniform.
- Switching normal form (BFS tree of H(5) switched to 0; 15,625 cotree voltages): 1016-1064 per value. Uniform: the
  hexagon part cannot be switched to a few values.
- Apartment holonomies (sum of hexagon voltages around 12-cycles, gauge invariant): fraction zero 0.038 (q=3 Z24,
  uniform 0.042), 0.052 (q=4 Z20, 0.050), 0.069 (q=5 Z15, 0.067). Matching-cycle holonomies are uniform too.
- Walk-sum dispersion (Var_g/Mean_g of non-backtracking walk counts per (point, line) pair): valid q=3 Z24 0.938,
  valid q=4 Z20 0.948, valid q=5 Z15 0.934, random q=5 Z15 0.932; the multinomial value 1-1/m is 0.958, 0.950, 0.933.
  Valid lifts have exactly the statistics of random lifts.
- Matchings-only lifts (hexagon voltages 0): dispersion 1.22-1.31 (clumped: walks with the same matching sequence
  collide). Their random cost is 1.5-2x that of full random lifts at the same m (q=3, m=28: 435-494 against 230-255).
  The hexagon voltages are what decorrelates the walk sums.
- Mutual information between a raw hexagon voltage and each point coordinate (q=5 valid): at the sampling-bias level.
- Switching fact: a hexagon voltage of the form f(p)+g(l) is switching-trivial (it is zero on hexagon edges after changing
  the matchings). Formulas only matter through flag-dependent voltages.
- Matchings-only annealing (HZERO=1, runs/exp_hzero.sh): Z12, Z16, Z20, Z24 valid (Z24 in 3479 steps); Z28 best 28.
- Not done: automorphism-invariance of the valid unrestricted lifts (superseded by section 4).

## 3. Formula families tested (all negative, unrestricted search space)

- Constant matching voltages (mv_1 = a, mv_2 = b, hexagon 0, all (a,b), runs/constscan_q3.txt): best point costs 11
  (m=16), 586 (m=20), 20007 (m=24). Random lifts: about 0 (m=16), about 4 (m=20), about 45 (m=24). Dead.
- q=3, m=24 (150 samples; median of point cost + dup penalty): random 46 (min 28); hexagon voltages in {0, 12} 78
  (min 47); bilinear B(x_p, x_idx(l))*c 58 (min 32). Layer-based table eps[(dist(p0,p), dist(p0,l))] at q=3, m=20:
  median 11, min 2 (random: median 4, min 0).
- q=5, m=16 (60 samples each): runs/fam2_q5_m16.txt (random median 62, min 36).

## 4. K-symmetric lifts (src/symgroup_np.py, src/symlift.c, src/symlift_ea)

### 4.1 Construction
- Aut(H(q)) by BLISS (src/autg.py via python-igraph in pylib): |Aut| = 8,491,392 = 2|G2(3)| (H(3) is self-dual),
  5,859,000,000 = |G2(5)| (q=5), 664,376,138,496 = |G2(7)| (q=7). Side-preserving elements (G2(q)) only.
- K = <k>, k of prime order P, acting fixed-point-freely on points and lines (random words in the generators, then a
  power of prescribed order; src/symgroup.py, symgroup_np.py). Found: q=3 P=13 (28 point orbits) and P=7 (52);
  q=4 P=13 (105) and P=7 (195); q=5 P=31 (126); q=7 P=43 (456). Composite orders (86, 172, 344) were not found.
- Lift invariant under K: hexagon voltages constant on flag orbits; matchings equivariant, sigma_t(k^j p_i) =
  k^(j+c_t(i)) l_{tau_t(i)} with tau_t a permutation of the point orbits and c_t(i) in Z_P; matching voltages constant on
  point orbits. Variables: N(q+1)/P flag-orbit voltages, s matching voltages per matching, tau and c.
- Cost: uncovered (line, g) sums over the s orbit representatives (weight P), dup penalty 100 per double edge. Moves:
  one flag-orbit voltage, one matching voltage, one offset c, a swap in tau. Metropolis with geometric cooling; the
  candidate's cost is evaluated with an early abort at the acceptance cap (symlift_ea; same trajectory as symlift).
- Checks: symlift's cost equals hexeval's full cost on the same file (q=3 random: 13 = 13), and the best lifts are
  re-checked by hexeval (full) and src/indep.c (explicit BFS from all base sources, DIAMETER_OK).

### 4.2 Results (units: Z_m copies; "valid" = cost 0 with explicit BFS check where marked)

| q | Delta | table m | K (P, orbits) | m | iterations | result | file |
|---|---|---|---|---|---|---|---|
| 3 | 6 | 20 | Z13 (28) | 24 | 87 | valid (indep DIAMETER_OK) | runs/sym_q3_p13_m24.sol |
| 3 | 6 | 20 | Z13 (28) | 28 | 4848 | valid (indep DIAMETER_OK) | runs/sym_q3_p13_m28.sol |
| 3 | 6 | 20 | Z13 (28) | 30 | 8000 | cost 13 (1 unit) | runs/sym_q3_p13_m30_s101.* |
| 3 | 6 | 20 | Z13 (28) | 32 | 8000 | cost 39 (3 units) | runs/sym_q3_p13_m32_s102.* |
| 3 | 6 | 20 | Z7 (52) | 28 | 8000 | valid (indep DIAMETER_OK) | runs/sym_q3_p7_m28_s103.sol |
| 3 | 6 | 20 | Z7 (52) | 30 | 8000 | valid (indep DIAMETER_OK), 21,840 vertices | runs/sym_q3_p7_m30_s104.sol |
| 3 | 6 | 20 | Z7 (52) | 32 | 8000 | cost 98 (14 units) | runs/sym_q3_p7_m32_s105.* |
| 4 | 7 | 20 | Z13 (105) | 20 | 8000 | valid (indep DIAMETER_OK), 54,600 vertices | runs/sym_q4_p13_m20_s112.sol |
| 4 | 7 | 20 | Z13 (105) | 24 | 8000 | cost 130 (10 units) | runs/sym_q4_p13_m24_s106.* |
| 4 | 7 | 20 | Z13 (105) | 28 | 8000 | cost 2847 (219 units) | runs/sym_q4_p13_m28_s107.* |
| 4 | 7 | 20 | Z13 (105) | 32 | 8000 | cost 13598 (1046 units) | runs/sym_q4_p13_m32_s108.* |
| 4 | 7 | 20 | Z7 (195) | 24 | 1190 of 8000 (stopped) | best 61 units | runs/sym_q4_p7_m24_s109.log |
| 5 | 8 | 25 | Z31 (126) | 20 | 1866 | valid (indep DIAMETER_OK), 156,240 vertices | runs/sym_q5_p31_m20.sol |
| 5 | 8 | 25 | Z31 (126) | 21 | 8000 | best 4 units (124) | runs/sym_q5_p31_m21_s111.* |
| 5 | 8 | 25 | Z31 (126) | 22 | 8000 | best 17 units (527) | runs/sym_q5_p31_m22.* |
| 5 | 8 | 25 | Z31 (126) | 25 | 6148 (stopped mid-schedule) | best 294 units (9114) | runs/sym_q5_p31_m25.log |
| 7 | 10 | 30 | Z43 (456) | 20 | 2372 of 2500 (time limit 40 min) | best 13 units (559), hexeval full check 559 | runs/sym_q7_p43_m20.* |

Unrestricted annealing for comparison: q=3 Z24 valid (c6, 2133 steps), Z28 stalls at 12 (c6); q=5 Z15 valid, Z16 stalls
at 30 (c6); q=7 best 17 (c6). So K-symmetry gives +6 copies at q=3 (30 against 24) and +5 at q=5 (20 against 15); at q=4 it
gives the same 20 as the unrestricted search.

Unrestricted q=4: c6 Z20 valid; the symmetric Z20 lift above is the same table value found with 105 orbit variables.

### 4.3 Reading
- The first-moment ratio E/L is the same for symmetric and unrestricted lifts (both numerator and denominator scale
  with 1/P), so the symmetric gain is in the search, not in the existence threshold.
- Symmetric annealing at q=4 (K=Z13, Z7) reaches 20 but not 24: the gain is not uniform across q. q=3 (small N, many
  orbits per copy) is the favourable case.
- q=5 frontier with this annealer: 20 valid, 21 cost 4 units, 22 cost 17 units. Table 25 is not reached.
- Frontier by q (this annealer, 8000-step schedules unless noted): q=3 30 (table 20), q=4 20 (table 20), q=5 20
  (table 25), q=7 not 20 (table 30; 2500 steps). The gap to the table grows with q, consistent with the first-moment
  picture (section 1).

### 4.4 q=7, K = Z43 (456 orbits)
- One symmetric evaluation takes about 1.1 s (456 sources, 3 lanes of 20 bits per pass, early abort). Run at m=20,
  2500 steps, time-limited at 2,400 s (last improvement at step 2,372, temperature 0.06): best 13 units = cost 559
  (plain), not valid. Start cost 197 units (random symmetric lift). So m=20 needs far more steps than this; no conclusion about 30.

## 5. What this means for the cell (10,8)

- Random-like constructions cannot reach m = 30 at q = 7 (E/L = 1.21); 31 needs anti-correlated walk sums.
- The symmetric search is the first route in this session that goes past the unrestricted annealer's frontier. Its
  frontier falls with q (q=3: 30 against table 20; q=5: 20 against table 25); whether it reaches 30 at q=7 needs far
  more CPU than one hour per run. A longer q=7 run (or a larger group: composite orders were not found by random
  words) would be the next step.
- Checks to use for any candidate: explicit BFS (src/indep.c), and walk dispersion (src/wcount.c): random survivors give
  1-1/m; a structured family should be clearly below it.

## Files

- src/hexgen2 (H(7) built: hex/hex_q7.bin), src/hexeval, src/indep, src/lift3, src/hexcheck (copies of c6 tools).
- src/wcount.c (walk multiplicities; validated: 47 = hexeval 47 on a random lift, 0 on the valid lift), src/holo.py,
  src/structan.py, src/thr.py (thresholds), src/fam.py, src/fam2.py (family writers and evaluators).
- src/autg.py (BLISS generators), src/symgroup.py and src/symgroup_np.py (semiregular K), src/symlift.c (symmetric
  annealer; symlift_ea = same with early-abort cap; the flag-orbit table no longer needs N x N memory).
- runs/: exp_hzero.sh, scan2.sh, p0_q3.sh, constscan_q3.txt, fam2_q5_m16.txt, sym_* (symmetric runs), K_q*_p*.txt
  (the K permutations), autgens_q*.txt (BLISS generators), sym_batch_summary.txt, sym_q5_summary.txt.
- sols/: copies of c6's valid unrestricted lifts.
