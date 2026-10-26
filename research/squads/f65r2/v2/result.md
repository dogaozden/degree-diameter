# Verification card v2: C49:C7 has no 6-set S with both conditions

## Result

No 6-element subset S of G = C49:C7 (order 343, (x,j)(y,k) = (x + 8^j y mod 49, j+k mod 7)) satisfies both
(S^-1 S)^2 = G and (S S^-1)^2 = G. The claim is confirmed by an independent search.

| quantity | value |
|---|---|
| sets checked (reduced enumeration, see Reductions) | 79,558,106 |
| (= C(341,4) = 553,526,545 sets with e in S, of which 474,298,440 were removed by the stabiliser reduction) | |
| min uncovered for condition 1, over all checked sets | 0 |
| sets satisfying condition 1 (reduced enumeration) | 78 |
| min uncovered for condition 2 among the 78 condition-1 sets | 6 |
| sets satisfying both | 0 |

Cross-checks:
- Fast coverage (D-list products) against brute force over all 4-tuples x1^-1 x2 x3^-1 x4 (and x1 x2^-1 x3 x4^-1)
  on 79 sampled sets during the run: 0 mismatches.
- The 78 condition-1 sets were re-verified in a separate Python script (`verify_cond1_sets.py`, group law taken straight
  from the formula, coverage by literal 4-fold products): all 78 satisfy condition 1, min uncovered condition 2 = 6, none
  satisfies both.
- Positive test (C49:C3, order 147, (x,j)(y,k) = (x + 18^j y, j+k mod 3)), same program, K = 6:
  1,584,258 reduced sets satisfy both conditions (cond1 sets 1,949,145), with 3,921 brute-force cross-checks and 0
  mismatches. Example: S = {0, 49, 1, 2, 3, 102} (indices x + 49 j) satisfies both.
- Reduction test on C49:C3: without the stabiliser reduction (21.2M sets) the minimum uncovered values are the same
  (cond1 0, cond2 0), and the stabiliser reduction removes exactly a factor 42 on iteration 0 (stabiliser order 42).

## Group and automorphisms

- 8 has order 7 mod 49 (8^7 = 344 = 7*49 + 1), and the relation b a b^-1 = a^8 holds for a = (1,0), b = (0,1).
- Aut(G) computed by brute force: every pair (u,v) with u^49 = 1, v^7 = 1, v u v^-1 = u^8 defines phi(a^x b^j) = u^x v^j;
  kept if bijective and a homomorphism on all 343^2 pairs. |Aut(G)| = 2058.
- Aut-orbits on the 342 non-identity elements: sizes 294, 7, 7, 7, 7, 7, 7, 6.
- Stabiliser of the representative of the 294-orbit: order 7.

## Reductions (justification)

1. WLOG e in S. For g in G: cond1 is invariant under S -> gS (since (gS)^-1(gS) = S^-1S) and cond2 is conjugated by g;
   cond2 is invariant under S -> Sg (since (Sg)(Sg)^-1 = SS^-1) and cond1 is conjugated by g^-1. A conjugate of G is G, so
   both satisfaction properties are unchanged. Any nonempty S can be right-translated to contain e.
2. Aut(G) maps (S^-1S)^2 to (phi(S)^-1 phi(S))^2 and similarly for cond2, so S may be replaced by phi(S).
3. Orderly enumeration: iteration k fixes r_k = the representative of the k-th Aut-orbit (orbits sorted by decreasing
   size) and takes the other 4 elements from orbits with index >= k, excluding r_k. Any S containing e has a smallest
   orbit index k among S\{e}; an automorphism moves one such element to r_k, and every element of phi(S) lies in an orbit
   of index >= k, so phi(S) is enumerated.
4. In iteration 0 (r_0 in the 294-orbit), the 4-subsets are further reduced by the 7-element stabiliser of r_0: a subset T is
   kept only if its sorted tuple is lexicographically minimal among its images under the stabiliser. Each stabiliser orbit
   keeps exactly one representative. (Validated on C49:C3 as above.)

Iteration sizes (pool sizes in brackets): iter 0 (341): 79,228,105 evaluated; iter 1 (47): 178,365; iter 2 (40): 91,390;
iter 3 (33): 40,920; iter 4 (26): 14,950; iter 5 (19): 3,876; iter 6 (12): 495; iter 7 (5): 5.

Note: the 78 condition-1 sets are representatives in this reduced enumeration, not Aut-by-translation classes, so the count is
not directly comparable to the director's 29 classes.

## Files

- Program: `/home/user/degree-diameter/research/squads/f65r2/v2/work/search.c` (compiled as `search2`, gcc -O3). Usage:
  `./search2 groupfile K outfile [check_every] [use_stab]`.
- Group files and Aut/orbit generator: `/home/user/degree-diameter/research/squads/f65r2/v2/work/setup_group2.py`
  (`python3 setup_group2.py 49 7 8 g343b.txt`; `python3 setup_group2.py 49 3 18 g147b.txt`).
- Main run output: `/home/user/degree-diameter/research/squads/f65r2/v2/work/g343_K6.log`, condition-1 sets with their
  condition-2 uncovered counts: `/home/user/degree-diameter/research/squads/f65r2/v2/work/g343_K6_cond1_sets.txt`.
- Python re-verification: `/home/user/degree-diameter/research/squads/f65r2/v2/work/verify_cond1_sets.py`.
- Test logs: `/home/user/degree-diameter/research/squads/f65r2/v2/work/test147_K6_stab.log`,
  `/home/user/degree-diameter/research/squads/f65r2/v2/work/test147_K6_nostab.log`.

Director's code in research/fresh65/tools/ was not read or reused.
