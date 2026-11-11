# e14: hole anatomy of the (4..6,10) near misses, and a Sidon-type constraint on S

Setting: Haar graph H(G,S), G = Z_m x|_r Z_k, n = 1, |S| = d (S contains e), vertices (g,A),(g,B), edges (g,A)~(sg,B),
D = 10. Scripts in this folder: anatlib.py (parse, group, BFS), anat2.py (per-j-fiber reach), quot.py (quotient walk
counts), holes_dist.py (true distances), rstats.py (random-S statistics), sidon_search.py and climb.py (constrained search).
No solution was found, so nothing needs a checker run; no scoreboard score.

## 1. Holes of the three near-miss states (true distances, from holes_dist.py)

- (4,10) r1/c09/g6275_s61b.best, G = Z251 x| Z25 (r = 25), d = 4, S j-projection {0,21,12,7}. Cost 2 on each side.
  From (e,A) the unreached B-vertices are (a,j) = (209,24) and (222,5); from (e,B) the A-vertices are (46,1) and (54,20).
  Both sides have distance histogram [0,4,0,36,0,323,0,2408,0,3502,0,2]: the two holes are the only vertices at distance 11.
  Each hole is the single unreached element of its j-fiber (fiber j = 24, 5, 1, 20 has 250 of 251 elements reached). The
  holes come in inverse pairs: A-side j-values {-1, 5}, B-side {1, -5}.
- (5,10) r1/c11/a8_1453_33.sol.best, G = Z1453 x| Z33 (r = 11), d = 5. From (e,A): (851,18), (1034,27); from (e,B): (120,6),
  (536,15). All four holes have distance 11 and j in 3*Z33 minus 0, i.e. j-order 11.
- (6,10) r1/c13/g41_best.sol, G = Z6397 x| Z41 (r = 5330), d = 6, cost 3. From (e,A): (4546,9), (5750,25), (6277,20).
  From (e,B): (3855,21), (4586,32), (6220,16). All at distance 11.

Summary: in all three states every hole is at true distance 11 = D + 1, and the ball of radius 9 is already within a few
elements of N. The holes are the last tail of the distance layers (layer sizes grow about x9 per two steps up to
layer 5, then saturate). The quotient walk counts (quot.py) do not single out the holes: the j-values with the fewest
alternating walks are not the hole j-values, so the "few walks per j-fiber" explanation is ruled out.

## 2. Random S statistics (rstats.py, uniform random S with e, D = 10; hole rate = unreached vertices per vertex per side)

| group (d) | sampling | samples | hole rate | cost median / min | class skew (ratio to overall) |
|---|---|---:|---:|---|---|
| Z251 x| Z25 (4) | uniform | 30 | 5.0e-2 | ~50 / 14 | j-order 25 (units) 1.13; kernel j = 0 0.26 |
| Z251 x| Z25 (4) | j-projection distinct and generating | 30 | 1.3e-2 | ~44 / 14 | none (0.96-1.24) |
| Z251 x| Z25 (4) | Sidon (below) | 30 | 1.1e-2 | ~40 / 10 | none (0.99-1.05) |
| Z1453 x| Z33 (5) | uniform | 10 | 6.0e-2 | ~85 / 45 | j-order 3 (j = +-11) 1.77; kernel 0.01 |
| Z1453 x| Z33 (5) | Sidon | 12 | 2.2e-3 | ~40 / 12 | none (0.99-1.12) |

The uniform sampling has a clear class skew: the kernel fibers (j = 0) are almost never holes, and the fibers that
carry the hole mass are the non-kernel j-fibers with small j-order (units for k = 25, the order-3 subgroup for k = 33).
The constraint removes the skew and cuts the hole rate by 4.5x (k = 25) and 27x (k = 33).

## 3. Constraint tested: Sidon-type j-projection

Constraint: the quotient elements j_s (s in S, j-coordinates in Z_k) are distinct, and all d(d-1) ordered differences
j_s - j_t (s != t) are distinct and nonzero in Z_k. For d = 4 that is 12 distinct nonzero differences among the 24 nonzero
residues of Z_25; for d = 5 it is 20 distinct differences in Z_33. The constraint is only on the quotient Z_k, so
it keeps the H(G,S) structure and is cheap to sample (rejection). It is a covering-style condition, not a proof device.

Search with the constraint, (4,10), S = {e} + 3 random:
- sidon_search.py, 80 s: 342 valid samples, best cost 8: S = [(0,0),(38,16),(146,14),(240,4)] (best_4_10_sidon.sol).
- climb.py, 70 s, 1-element random replacement with plateau moves (Sidon kept): 897 iterations, no gain.
So the constraint lowers the typical cost but does not reach the near-miss cost 2; the cost-2 states remain outliers
of a much larger search, consistent with round 1.

## 4. Not done

- (6,10) Sidon statistics: the run timed out (rejection sampling for 30 differences in Z41 plus the d = 6 BFS).
- Holes of the Sidon states were not analysed (only costs are known).
- The "size law" comparison with exp(-lambda) was not made quantitative: the walk count with multiplicity (4^L sequences)
  is far above N, so the Poisson count of distinct words needs a proper collision model.

## Verdict for the card

No raise. Best constrained cost for (4,10) is 8 (climb: 8). Holes are distance-11 tails, one per fiber, and the class
skew of random S disappears under the Sidon-type constraint on the j-projection.

## 5. Addendum: Sidon search on (5,10)

sidon_search.py on Z1453 x| Z33 (d = 5), 80 s, 41 valid samples: best cost 22 (best_5_10_sidon.sol). Far from the
cost-2 near miss, so the constraint helps the typical S but not the extreme tail.
