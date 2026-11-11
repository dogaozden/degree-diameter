# Small-q tests for research/theorems/D7_HEXAGON.md

Independent of the lab's hexagon generators (hexgen*.c, typed5*.c): H(q) is built here from coordinates, and every
graph is checked by research/lifts/coordinator_check/apsp_mt.c (all sources, no symmetry assumed; VALID means
bipartite, max degree <= d, diameter <= D). All positive tests below are RESULT VALID; the only INVALID / far pairs are
the negative controls, as intended. Total run time of everything: under a minute (q <= 5).

## H(q) from coordinates (hexq.py)

Points: the points of Q(6,q): X0X4 + X1X5 + X2X6 = X3^2. Lines: the lines of Q(6,q) whose Grassmann coordinates
p_ij = x_i y_j - x_j y_i satisfy

    p12 = p34,  p54 = p32,  p20 = p35,  p65 = p30,  p01 = p36,  p46 = p31.

Note: the version with p20 = p36 and p01 = p35 (as first quoted) is WRONG with this quadric: at q = 3 some points then
have only q = 3 collinear points instead of q(q+1) = 12, and H(2) gets 39 lines instead of 63. The version above is the
one homogeneous under the torus t0 t1 t2 = 1, t4 = 1/t0, t5 = 1/t1, t6 = 1/t2, t3 = 1; a search over all 64 sign patterns
of it found exactly two that work (all signs +, and all six right-hand sides negated). Validated (logs/hexq_Q.log) for
q = 2, 3, 4, 5:

| check | q = 2 | 3 | 4 | 5 |
|---|---|---|---|---|
| N = (q^6-1)/(q-1) points, N lines, q+1 points per line, q+1 lines per point | OK | OK | OK | OK |
| incidence graph connected, diameter 6 | OK | OK | OK | OK |
| distance profile 1, q+1, (q+1)q, ..., (q+1)q^4, q^5 from every vertex (girth 12) | all | all | all | 1 in 15 |
| two points at incidence distance <= 4 iff B(x,y) = 0 (polar form x0y4+x4y0+x1y5+x5y1+x2y6+x6y2-2x3y3) | all pairs | all | all | 1/300 rows |

Hermitian spread: the H(q)-lines inside the hyperplane x0 = c x4 + e x3 whose section has (q+1)(q^3+1) points
(elliptic): c, e = 1, 1 (q = 3), 1, 2 (q = 4, GF(4) element 2 = the root w of w^2 + w + 1), 1, 2 (q = 5). In each case
exactly q^3 + 1 lines (28, 65, 126), pairwise at incidence distance 6, (q+1)(q^3+1) distinct points on them.

## T-G1 (the key test): friendly transitions with (G1) sets, no hubs (t_g1.py, logs/t_g1_q*.log)

(G1) for a set F of points: for every p in F, the points of F collinear with p lie on one line through p (whole lines,
collinear pairs, triples on a line all allowed). Dual (G1) for line sets. Sets: (a) all points on the q^3+1 Hermitian
spread lines, (b) random greedy maximal (G1) sets, also greedy (G1) completions of half the spread, (c) (R1) sets:
every point has exactly one partner ("pairs only"), or at most one, with NO hub constraints at all, (d) line sets:
all lines through the points of a greedy partial ovoid (pencils), greedy dual (G1) sets, (R1) line pairs.
Two-level graph = levels H and D (or D and H for line sets) with the identity matching minus F, d = q + 2. Five-level
graph = types H D H D H, r = 2, the six friendly transitions freed with (G1) sets (different families on different
transitions), the four others random bijections, nothing freed there, d = q + 3. Main graphs only, no hubs.

| q | two-level, point sets (|F|, collinear pairs) | two-level, line sets | HDHDH (n) | result |
|---|---|---|---|---|
| 3 | spread 112 (168), greedy 79, 79, half-spread+greedy 103 (146), R1 pairs 66, R1 71 | pencils 64 (96), greedy 77, 80, R1 pairs 68 | 3,640 (2 variants) | all VALID d=5 / d=6, D=7 |
| 4 | spread 325 (650), greedy 203, 204, 295 (544), R1 pairs 170, R1 196 | pencils 95 (190), greedy 210, 208, R1 pairs 174 | 13,650 (2) | all VALID |
| 5 | spread 756 (1,890), greedy 444, 445, 729 (1,762), R1 pairs 376, R1 428 | pencils 216 (540), greedy 443, 436, R1 pairs 372 | 39,060 (2) | all VALID |

Repeated with seeds 2 and 3 (logs/t_g1_q*_seed*.log): 12 of 12 VALID in each of the 6 runs.
The spread-point sets reach (q+1)(q^3+1) (112, 325, 756), more than the non-collinear Hoffman bound q^4+q^2+1
(91, 273, 651).

Negative controls (two-level H -> D, a maximal (G1) set plus one point, so (G1) fails), far ordered pairs (d > 7) by
farcount.c: q = 3: 432 (spread + 1), 72 / 192 / 168 (greedy + 1, seeds 1-3); q = 4: 960, 192 / 128 / 288;
q = 5: 1,800, 360 / 320 / 80. apsp_mt on the q = 5 greedy+1 graph: diameter 8, RESULT INVALID (logs/t_g1_q5_neg_apsp.log).

## T-A: plain level covers, random bijections (t_ah.py, logs/t_ah_q*.log)

Types HHH, HDH (r = 1), HHHHH, HDHDH (r = 2), and for q = 3, 4 also HHDHHDD, HHHHHHH (r = 3); all VALID with
d = q + 1 + r, D = 7, regular of degree q + 1 + r. n = (2r+1)·2N: q = 3: 2,184 / 3,640 / 5,096; q = 4: 8,190 / 13,650 /
19,110; q = 5: 23,436 / 39,060.

## T-H: one-transition surgery with a non-friendly matching (t_ah.py)

M: points -> lines built by levels.local_duality_map: M(R) = f(R), M(mid(x,y)) = mid(f(x), f(y)) for pairs of R at
distance 4, the rest of each Gamma_2(r) onto the rest of Gamma_2(f(r)) at random, everything else at random; (H1),
(H2), (H3) re-checked directly on the final M (and on M^-1 with M(R) for the D -> D transitions).
Graphs: HHH (r = 1, the same M and R on all three transitions; the cell-13-7 construction, no hubs) and HDHDH (r = 2;
H -> H with (M, R), D -> D with (M^-1, M(R)), friendly transitions with spread points / greedy dual (G1) lines).

| q | R pairwise opposite (|R|) | HHH | HDHDH | mirrored R (|R|, pairs at distance 4) | HHH | HDHDH |
|---|---|---|---|---|---|---|
| 3 | 28 (an ovoid of H(3), found by greedy) | VALID | VALID | 17 (19) | VALID | VALID |
| 4 | 23 | VALID | VALID | 26 (21) | VALID | VALID |
| 5 | 33 | VALID | VALID | 38 (28) | VALID | VALID |

Negative control (two levels H -> H, (M, R) with R pairwise opposite): far ordered pairs 0 with M intact; after
swapping M at one point of Gamma_2(r0) with M at a point outside (for the q = 3 ovoid: a point of Gamma_2(r1)), so that
only (H3) fails: 50 (q = 3), 76 (q = 4), 126 (q = 5) far pairs.

## T-hub: full graphs with hubs (t_hub.py, logs/t_hub_q*.log)

Mirrored set (q = 4: |R| = 28, 1 pair at distance 4; q = 5: 35, 8 pairs), friendly transitions with spread points or
greedy (G1) sets. B-hubs: one free A-slot per level, A-hubs: one free B-slot per level (random assignment), hub graph a
union of q - r random matchings, redrawn until BFS from all hubs finds nothing beyond 7 (K lowered by 20% after every
10 failed draws). The free-slot minimum is reached for r = 1; for r = 2 the hub graph degree is only q - 2 and K had to
be lowered (to 48 at q = 4, 61 at q = 5; the slot minimum is 236 / 473).

| q | types | free A-slots / B-slots per level | K per side | n | result |
|---|---|---|---|---|---|
| 4 | HHH | 28 each | 28 | 8,246 | VALID d=6 D=7 |
| 4 | HDH | [325, 208, 28] / [28, 325, 208] | 28 | 8,246 | VALID d=6 D=7 |
| 4 | HDHDH | [353, 236, 353, 416, 237] / [236, 534, 236, 353, 236] | 48 | 13,746 | VALID d=7 D=7 |
| 5 | HHH | 35 each | 35 | 23,506 | VALID d=7 D=7 |
| 5 | HDH | [756, 446, 35] / [35, 756, 446] | 35 | 23,506 | VALID d=7 D=7 |
| 5 | HDHDH | [791, 481, 791, 892, 473] / [481, 1194, 481, 791, 481] | 61 | 39,182 | VALID d=8 D=7 |

## Not done

T-dual (a duality of H(3) and the all-H construction with M = phi and the spread points freed): a plain backtracking
search for the duality (BFS order, distance checks) did not finish in 10 minutes and was dropped. A single transition
with M = phi is the friendly transition after renaming level j+k by phi^-1, so T-G1 (a) covers the same graphs up to
isomorphism.

## Files and commands

- hexq.py: GF(q) (q = 2, 3, 4, 5, 7, 8, 9), H(q) from Tits' equations, validation, Hermitian spread.
- levels.py: typed level covers, transitions, freed sets, hubs; (G1) / (R1) / opposite greedy sets; local_duality_map;
  check_H123; mirrored_greedy.
- t_g1.py, t_ah.py, t_hub.py: the tests. dist.c (all-pairs distances of I), farcount.c (far pairs from a source list).

```
cd research/theorems/d7hex_tests
cc -O2 -o dist dist.c && cc -O2 -o farcount farcount.c && cc -O2 -pthread -o apsp_mt ../../lifts/coordinator_check/apsp_mt.c
for q in 2 3 4 5; do python3 hexq.py $q; done          # builds cache/hexQ.{npz,edges,dist}, validates
for q in 3 4 5; do for s in 1 2 3; do python3 t_g1.py $q $s; done; python3 t_ah.py $q; done
python3 t_hub.py 4; python3 t_hub.py 5
```
Generated graphs go to graphs/ (25 MB) and cache/ (67 MB), both git-ignored.
