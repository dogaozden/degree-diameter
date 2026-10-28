# c18 notes: wildcard = level graphs with unjoined level pairs (and the q=8 Tits-oval alternative, ruled out by counting)

## Order formula of the base family (Theorem A structure)
L levels, each level 2(q+1)(q^2+1) vertices (incidence graph of W(q)), every A-vertex has e external matching edges,
every B-vertex e external edges, degree q+1+e. Order n = L * 2(q+1)(q^2+1). Theorem A uses L = 2e+1 (regular tournament:
every pair of levels joined by one matching). Table: table.py (output in table_out.txt).

## Candidate 1 (not pursued): T2(O), q = 8, non-conic oval
Ruled out by arithmetic before construction: with the level family the order at q = 8 is L*1170 with L = 2e+1,
so the best q = 8 cell is Delta = 11 (5850 vs 7020, 0.833); hub gains are at most about 2(q^2+1) = 130 vertices.
Its order is the same as W(8) for the same q, so the Tits quadrangle cannot change any cell's order; it can only change
the freed-set / hub gains, which are about 1% of n. No validated predicted cell beats the q = 9 or q = 11 cells.
Not implemented in gqlib (only W, Q4, Q5, H3, AS are).

## Candidate 2 (pursued): level pairs NOT all joined by a matching
Claim tested: L > 2e+1 levels, each pair of levels joined by at most one matching (A-side out-degree <= e and B-side
in-degree <= e per level, so at most L*e matchings), with some pairs unjoined. The order would be L*2(q+1)(q^2+1).
Code: unjoined.py (random orientation + random bijections, checked by apsp), anneal.py (simulated annealing on
types, orientation, bijections; cost = # ordered pairs at distance > 5).

Results (all with apsp, D = 5, degree q+1+e):
- q=2, e=1: L=3 (regular, control) 200/200 pass; L=4 (2 pairs unjoined, 4 arcs) 0/300; L=5 (5 arcs) 0/300 random.
- q=3, e=2: L=5 control passes; L=5 with only 8 arcs (2 unjoined pairs) passes 155/200 random; L=6 and L=7 random 0/300.
- q=3, e=2, L=5 annealing: found and apsp-validated: found_q3_e2_L5_s1.txt (n=400, degree 6, types and arcs in
  the log line of anneal run).
- q=3, e=2, L=6 annealing: see run_q3_e2_L6.log (RESULT below).

## Results (final)
- q=3, e=2, L=6 (at most 12 matchings for 15 pairs, so at least 3 pairs unjoined), simulated annealing 6000 iterations:
  seed 2 best = 4580 bad ordered pairs (start 6196); seed 3 best = 404 bad ordered pairs (start 1382), out of 480^2.
  Not zero: no diameter-5 configuration with 6 levels found. Log: run_q3_e2_L6.log, run_q3_e2_L6_s3.log.
  (An L=7 run was stopped early with no result.)
- Validated (apsp RESULT VALID, D=5): found_q3_e2_L5_s1.txt, n = 400, degree 6 (= Theorem A family, L = 2e+1 = 5).
  Edge file format: first line n, then "u v" per line.

## Order/ratio table for the base family (table_out.txt)
Best q per Delta (L = 2e+1): Delta 13 -> q=9, n=11480 (0.9995 of 11486); Delta 15 -> q=11, n=20496 (0.9884 of 20736);
all other cells <= 0.90. Those are the existing level-graph numbers (PREAMBLE fact 7 and the 11,480 / 20,496 bases),
not new. The q=3 validation above predicts them only through Theorem A (checked by others for q <= 5), so nothing here
is an improvement.

## Conclusion for this card
- Tits oval T2(O), q = 8: cannot beat any cell (order equals W(8), best q=8 ratio 0.83). Not built.
- Unjoined level pairs: random and annealed search at q=2,3 never gives diameter 5 with more levels than 2e+1 in the
  cases tried (L=4 for e=1; L=6 for e=2; L=5 with 2 unjoined pairs does pass, but L stays 2e+1 in order terms).
  Count: with L levels, each level pair needs one matching, out-degree <= e on A-side and in-degree <= e on B-side, so
  at most L*e matchings, and L(L-1)/2 pairs; unjoined pairs must be bridged by 2-matching paths, which the random and
  annealed search did not achieve at L = 2e+2.
- 2-factors instead of matchings only cost more degree per pair (sum of weights over a level <= 2e), so they cannot
  raise L.
- Score: best (n/record) over cells predicted by a validated construction = 11480/11486 = 0.9995 (Delta = 13), but that
  is the existing level-graph family, not a new gain from this card.
