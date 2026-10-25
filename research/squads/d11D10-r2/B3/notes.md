# B3: why does k = 10 (single orbit) lose more than k = 5?

Card: the k = 10 orbit (psl 243 x Z11, alpha of order 10) costs about 9.5 clumps (mean 95), against about 7 predicted for a
random S. Mechanism claimed: s_(i+5) = (h x_i h^-1, -z_i) forces word identities (equal words of length <= 9 for every
generator). Budget 4 slot-min (used about 2.4); time box 40 min.

## 1. The orbit (derived by hand, checked numerically)

- alpha(x, z) = (h F(x) h^-1, 2z), h = [[0,1],[2,0]] over GF(3^5) = GF(3)[t]/(t^5+2t+1), F = entrywise Frobenius (order 5).
  h^2 = -I, so h is an involution of PSL(2,243), and F(h) = h.
- alpha^5(x, z) = (h x h^-1, -z) =: phi(x, z), an involutive automorphism; S = {e} + orbit is phi-invariant.
  With sigma_j = (F^j x, c_j z), c = (1, 9, 4, 3, 5), the orbit is {sigma_j, phi(sigma_j)}: five pairs with h-conjugate
  Q-parts and opposite z-parts.
- Checked in Python (ident_walks.py asserts): alpha is a homomorphism, alpha^10 = 1, alpha^5 = (c_h, -1).

## 2. Formal identities (equal for every generator): none up to length 7

A walk l_1..l_L (non-backtracking, e a letter) has B-side value l_L l_(L-1)^-1 ... l_1 (odd L). Test with K random generators
(equal keys = identity; accidental agreement ~ N^-K).

| run | B-side walks | duplicated walks | source |
|---|---|---|---|
| k = 10, length <= 5, K = 3 | 111,111 | 0 | ident_walks.py, ident_k10_L5.log |
| k = 5 (two orbits), length <= 5, K = 3 | 111,111 | 0 | ident_walks.py, ident_k5_L5.log |
| k = 10, length <= 7, K = 2 | 11,111,111 | 0 at every length | ident7.c, ident7_k10_L7.log |
| k = 5, length <= 7, K = 2 | 11,111,111 | 0 at every length | ident7.c, ident7_k5_L7.log |

Length 9 (1.1e9 walks) was not attempted. So the card's mechanism, read as identities holding for every generator, is
refuted up to length 7.

## 3. Ball sizes and costs (psl 243 x Z11, N = 78,917,652; LEVELS and RANDORB/RANDSAMPLE)

Walk counts without coincidence: r=5: 111,111; r=7: 11,111,111. Random S: r=5 deficit about 119 (6 samples), r=7 count
about 10,350,013 (6 samples).

| generator set | samples | cost (uncovered) | r=5 deficit (walks - distinct) | r=7 distinct vs random |
|---|---|---|---|---|
| plain random S | 40 | min 51, p10 55, **median 63** | about 119 (6 samples) | reference |
| k = 5 (two orbits, alpha = F, z -> 3z) | 40 | min 40, p10 47, **median 61**, mean 67.1, p90 95, max 118 | median 100 | -0.06 % (none) |
| k = 10 | 40 | 1 degenerate (71,743,320: all letters in PSL x {0}, so z_0 = 0; covered = |PSL| exactly); 39 others: min 40, p10 61, **median 91**, mean 103.3, p90 171, max 213 | median 550 (mean 676; max 2050) | -1.22 % of walks (mean 135 k short) |

Notes:
- The k = 10 shift is in the bulk (median 91 against 61-63), not only in a tail. 14 of the 39 non-degenerate k = 10 samples
  have cost > 100, against 3 of 40 for k = 5. This confirms the card's order of magnitude (its 95 is consistent with my mean 103).
- Within k = 10 the r=5 deficit correlates with cost: Pearson r = 0.69 over the 39 non-degenerate samples. The short-walk
  coincidences of a generator predict its cost. k = 5 has no such excess.
- Costs-to-lambda: median 91 gives lambda_eff = 13.67 (2.9 % of walks lost); mean 103 gives 3.8 %. k = 5 median 61 gives
  0.04 %; k = 5 mean 67 gives 0.7 %; random median 63 gives 0.3 %.

## 4. Where the k = 10 coincidences come from (one generator at a time, walks of length <= 5, ident_pair.py)

Duplicated walks (same value for one generator), and how many duplicate walks sit in a group containing a walk with an
h-pair adjacency (a step sigma_j -> phi(sigma_j)):

| generator | duplicated walks | in groups with a pair-adjacent walk |
|---|---|---|
| k = 10, seed 1 | 1,250 | 910 (73 %) |
| k = 10, seed 2 | 850 | 140 (16 %) |
| k = 10, seed 3 | 260 | 40 (15 %) |
| k = 5, seed 1 | 95 | 0 (no pairs) |

Chance level for a random generator: about 78 (the birthday count for 111,111 elements in N = 78.9 M).
So the pair adjacencies explain part of the k = 10 coincidences for some generators, but most come from other relations.
These coincidences are not formal identities (section 2), so they depend on the generator.

## 5. Structural reasons (k = 10 single orbit)

(a) Every order-10 alpha that puts 10 distinct Q-parts into S has alpha^5 = beta, an involutive automorphism with nontrivial
Q-part (conjugation by an involution of PSL, centraliser 244, or by an outer diagonal element, centraliser 242). So pairs
(x, beta x) cannot be avoided in a single 10-orbit. If beta were trivial on the Q-part, S would have six distinct Q-letters
and at most 10,365,630 Q-words of length <= 9, lambda_Q = 1.445 times |PSL(2,243)|; a Poisson estimate then leaves about 24 %
of the Q-part uncovered. That choice is impossible (an estimate, not a proof).
(b) For a pair walk the commutator x -> h x^-1 h^-1 x is 244-to-1 onto 29,403 values. Only the pure pair walks are concentrated
(about 20 of length 3), so this alone does not explain the loss.
(c) k = 5 with two orbits has alpha^5 = 1 and no pairs; it shows no excess coincidences (section 4).

## 6. Conclusion

- The k = 10 excess is real in my 40 samples: median cost 91 against 61-63 for k = 5 and random S. It accounts for about 3 %
  of the walks, consistent with the card's estimate.
- Its mechanism is short-walk coincidences that depend on the generator (r = 0.69 with cost). These are not word identities
  for every generator, so the card's stated mechanism is refuted up to length 7 (length 9 unchecked).
- The h-pair adjacencies are part of it for some generators (73 % in one case, 15 % in two others). Most coincidences in
  the other generators come from relations I did not identify.
- Order-10 alternatives: none avoids pairs (5a). The practical alternative is the k = 5 two-orbit family, which has no pairs
  and no excess coincidences in this data.
- Open: log the generators of the high-cost k = 10 samples (A2's DUMP binary) and classify their coincidences; a generator
  sub-family that avoids them would tell whether the loss is avoidable within k = 10.

## 7. Caveats

- 40 + 40 samples; the generator of each sample was not logged, so the degenerate type (z_0 = 0) is an inference from the covered count.
- Formal identity tests used 2-3 random generators (they cannot see identities that hold only for a sub-family).
- Length 9 identities were not tested; r = 7 numbers are counts of distinct elements, not costs.

## 8. Runs (all through the gate; no B3 process left)

run_ident.sh (k10 and k5, length <= 5, K = 3), run_all_b3.sh (ident7 both lengths <= 7; LEVELS 3 + 3; RANDSAMPLE 40),
run_levels40.sh (k10 and k5, 40 samples each, LEVELS=40), run_pair.sh (ident_pair.py, three k10 generators and one k5).
Logs: ident_*.log, levels.log, random40.log, levels40.log, pair.log, plus the 40-sample tables k10_levels_r3_r5_r7_cost.txt
and k5_levels_r3_r5_r7_cost.txt.
