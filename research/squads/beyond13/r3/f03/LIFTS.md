# f03: why cyclic lifts beat Haar graphs at Delta = 3, and how far they go (round 3, card f03)

Scripts: walks.py (nonbacktracking walks -> net traversal vectors), cover.py (random Z_n voltages, coverage over
fibres), lcf.py (Tutte 8-cage). Numbers are computed unless marked "model".

## Key identity
A lift walk from (s,0) to (v,h) has voltage sum_e x_e a_e, x = net signed traversal vector. Distinct x with the same
endpoint are distinct classes in the universal abelian cover (H_1 = Z^beta, no 2-cells). So the number W of distinct x
is an exact upper bound on the (endpoint, voltage) pairs any walk set can cover in a Z_n lift. W < #walks exactly when
two different nonbacktracking walks have the same net traversal (commuting short cycles).
Nonbacktracking walks from a source: cubic 3*2^(L-1), 4-regular 4*3^(L-1).

## Task 1: GP(10,3) (b = 20, E = 30, beta = 11)
| D | walks (length <= D) | distinct W | ratio | W_v per endpoint (min..max) |
|---|---|---|---|---|
| 9 | 1,534 | 1,534 | 1.000 | 44..109 |
| 10 | 3,070 | 3,014 | 0.982 | 84..215 |
| 11 | 6,142 | 5,804 | 0.945 | 196..432 |
| 12 | 12,286 | 11,000 | 0.895 | 371..768 |
| 13 | 24,574 | 20,258 | 0.824 | 647..1,356 |
| 14 | 49,150 | 36,404 | 0.741 | 1,197..2,392 |

First collisions at L = 10 (girth 6).

Random uniform voltages (all 30 edges), coverage over all 20 fibres:
- D = 13, n = 100 (N = 2000): P(diameter <= 13) = 0.26 (120 trials); mean uncovered per fibre 1.68 (model 0.78).
- D = 14, n = 140 (N = 2800): P(diameter <= 14) = 0.63 (60 trials); mean uncovered per fibre 0.91 (model 0.14).
- Single fibre only (source 0, 300 trials, D = 13): n = 120: P = 0.28; n = 140: 0.10; n = 160: 0.01 (mean uncovered
  25.6, model 18.6). Random voltages reach n = 160 about once in 100 tries, so the search is needed.

Model (per fibre): mu = sum_v n (1 - 1/n)^{W_v}. The real uncovered count is about 1.4-1.7x the model, because
commuting cycles force voltage coincidences the model ignores. Largest n: model gives about 130-150 at D = 13
(found 160 by search) and about 250-300 at D = 14 (found 280).

## Task 2: b vs beta at D = 13 (cubic bipartite bases; each has 24,574 walks)
| base | b | beta | W | ratio | W_v (min..max) | model n (mu about 3) | N = b n |
|---|---|---|---|---|---|---|---|
| K3,3 | 6 | 4 | 2,830 | 0.115 | 387..541 | about 90 | about 540 |
| GP(10,3) | 20 | 11 | 20,258 | 0.824 | 647..1,356 | about 130-150 | about 2,800-3,000 (found 3,200) |
| Tutte 8-cage (girth 8) | 30 | 16 | 23,782 | 0.968 | 505..1,071 | about 115 (rough) | about 3,450 |

Reading: beta sets the polynomial regime. K3,3 (beta = 4) saturates at a few thousand classes. Large beta with large
girth keeps the exponential walk count. The Tutte 8-cage has the best ratio but more vertices per fibre, so its
predicted N is close to GP(10,3). Not a clear win without a test. Cheapest next step: lift search on it at n = 110-120.

## Task 3: Delta = 4 at D = 13, is n*b about 190,000 plausible?
Walks of length <= 13 from one source: 3,188,645.
- K4,4 (b = 8, beta = 9): W = 288,653 (ratio 0.091; per endpoint 25,116..46,543). Model n about 3,900, so
  N about 31,000. Far below 190,000 (girth 4 forces heavy collisions).
- High-girth 4-regular bipartite base with no collisions (ratio 1): mu = N exp(-W/N) with W = 3.19e6 gives mu about 5
  at N about 2.9e5 and mu about 0.02 at N = 190,000. So 190,000 is plausible only if the distinct ratio stays above
  about 0.66 at D = 13 (W about 2.1e6). That needs girth about 8 or more (the cubic girth-8 base has ratio 0.97 vs
  0.82 at girth 6). Not tested for 4-regular bases here. Verdict: plausible only with a high-girth 4-regular base;
  K4,4-type bases give about 3e4.

Caveat: the model is one-fibre and ignores voltage coincidences from commuting cycles (about 1.5x in the data). These
are upper-bound-style predictions, not solutions. This card produced no valid graph (score 0).
