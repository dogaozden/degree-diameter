# e11: why odd-order metacyclic groups win at (4,13), and which k to use

Setting: G = Z_m x|_r Z_k, Haar graph H(G,S), Delta = 4, D = 13 (h = 6), N = |G| = 92.5k-95.9k per side.
Tools: research/squads/beyond13/r2/e11/meta_holes.c (exact BFS on the Haar graph, both sides, cost as haar_gen3),
meta_eval (same with a fixed S, env FIXS, LIST=1 lists holes). Load on the machine was 14-22, so samples are few.

## 1. Structure of the candidates
- m prime and r of order k mod m: G is the Frobenius group Z_m : Z_k. Every element (a,j), j != 0, has order k;
  every (a,0), a != 0, has order m. Checked for m = 4903, k = 19: 4903 is prime, so r^j - 1 is a unit for j = 1..18.
- Centre: (a,0) is central iff (r-1)a = 0, and (r-1) is a unit mod prime m, so Z(G) = 1. No central clumps.
- No involutions (odd order). So neither odd-D clump of research/frontier/beyond11/ODD_D_HOLES.md is present: the
  involution term (exp(-lambda/2)) and the central term (exp(-lambda/h)) are both zero.
- The only symmetry is an automorphism of S-type under which S is invariant. Random S have none, so no alpha-clumps.

## 2. Measured coverage (fraction of G reached from (e,A) by words of length 12 = (S^-1 S)^6), random S
Random symmetric-free S = {e, 3 random elements}, D = 13, 150 samples for k = 3, 5 (heavy tails dominate the mean),
40 samples for the rest. "Cost" = holes on both sides (haar_gen3 definition). Mean cost and min cost are over the samples.

| k | m | r | mean cover | mean cost | min cost |
|---|---|---|---|---|---|
| 1 (cyclic) | 93157 | 1 | 0.0099 | 184,469 | 184,469 |
| 3 | 31051 | 3087 | 0.0606 | 175,010 | 170,644 |
| 5 | 18661 | 13702 | 0.729 | 50,639 | 23,104 |
| 9 | 10333 | 1362 (order 9) | 0.906 | 17,474 | 2,146 |
| 11 | 8537 | 3375 | 0.982 | 3,378 | 62 |
| 13 | 7177 | 3569 | 0.985 | 2,899 | 38 |
| 17 | 5441 | 2670 | 0.978 | 4,123 | 18 |
| 19 | 4903 | 4248 | 0.972 | 5,151 | 8 |
| 23 | 4049 | 3453 | 0.989 | 2,124 | 8 |
| 29 | 3191 | 1079 | 0.982 | 3,285 | 10 |
| 37 | 2591 | 2404 | 0.968 | 6,138 | 12 |

(k = 19 with r = 230, the group of the r1/c15 solution, 3 samples: cover 0.9985, cost 138-560.)
None of the random S of this family is a solution at D = 13; the valid ones come from search (r1/c15).

## 3. Near misses of the known (4,13) solution
The r1/c15 solution S = {(0,0), (1818,17), (4490,6), (4768,7)} in Z4903 x|230 Z19 is valid (my BFS: ecc_A = ecc_B = 13,
cost 0). Replacing its last generator by 40 random elements (near_miss.py) gives cost ~400-500 (capped count; the
side-A list is capped at 400 so these are lower bounds): side A 370-380 holes, side B 24-82, with ~94 % of the holes at
j != 0 (j = 0 holds 1/19 of the elements). So the solution is an isolated needle: one generator move destroys it, and
the holes are ordinary elements, not a special class. The j = 0 over-representation seen in a 3-sample random test
(27 % of holes) did not persist (6.5 % here).

## 4. Why k = 3 and small k fail (the empirical law)
- Cyclic (k = 1) covers 1 % of G: the word set is the sumset of T = S^-1 S (13 elements) taken 6 times, and in an
  abelian group that has at most C(18,6) = 18,564 values. Abelian bi-Cayley graphs are hopeless at any size.
- With k >= 2 each letter carries a class j in Z_k, and the a-part of a word is sum_i r^(J_i) a_i with J_i the partial
  sums of the j's. Only k coefficient classes r^c exist. For k = 3 the a-part is a Z[omega]-combination of four
  generators, and the words collapse to about 6 % of G. For k = 5 the cover is 73 %, k = 9 91 %, k >= 11 about 97-99 %.
  This is a measured threshold, not a proof; the exact count of distinct word values is the thing to derive.
- Rule of thumb from the table: take k prime with k >= 11 (the data: 11, 13, 19, 23 are all covered at ~98 %). k in
  [13, 23] at N ~ 1e5 is the good range. For larger N the same k works (the cover does not depend on m), so pick k
  from Delta and D, not from N: k >= 2h + 1 - 2 = D - 2 = 11 for D = 13 is the lowest value measured; k = 13 = D is the
  safe choice. (Hypothesis, to be tested at D = 11, 12 and 14.)
- Generic holes are not the problem: at k >= 11 the cover is high, but the search still needs the holes (about 3-6
  thousand per random S, mean) to cancel. The good orbit-free search of r1/c15 found cost 0 at k = 19.

## 5. Next
Test the rule k = D (prime) at D = 11, 12 (even D: check whether even D needs the same k) and at Delta = 3 and 5. Derive the
distinct-word count for Z_m x|_r Z_k with the class argument and compare with the measured cover above.
