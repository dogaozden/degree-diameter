# Frobenius groups Z_p x| Z_k for the small D = 11, 12 cells

Job beyond-d11b, 2026-11-01 (Opus director, Haiku squad rounds r1-r6, research/squads/beyond11b/). Summary of a lead
that came out of round 1 and raised five cells in rounds 1-3.

## Groups

G = Z_p x|_r Z_k: elements (a, j), a in Z_p, j in Z_k, (a, j)(b, l) = (a + r^j b, j + l), with p prime, k | p - 1 and
r of order exactly k mod p (haar_gen3 / build_haar2.py spec `meta p k r`). Then G is a Frobenius group with kernel Z_p and
complement Z_k, its centre is trivial, and for odd k its order pk is odd, so it has no involutions (r2/h17 NOTE.md,
section 1). Odd products F1 x F2 of two such groups also have trivial centre and no involutions.

## Results (plain random S of size Δ with e in S, annealed by haar_gen3; no automorphism orbits)

| cell | group | N = pk | vertices | was | check |
|---|---|---:|---:|---:|---|
| (4,11) | Z523 x\|_9 Z29 | 15,167 | **30,334** | 24,360 (PSL(2,29)) | build_haar2 + apsp |
| (5,11) | Z5023 x\|_2886 Z31 | 155,713 | **311,426** | 297,648 (SL(2,53)) | build_haar2 (+ apsp, see log) |
| (6,11) | Z20809 x\|_12972 Z51 | 1,061,259 | **2,122,518** | 2,094,960 (SL(2,29) x Z43) | build_haar2 |
| (4,12) | Z731 x\|_7 Z48 (731 = 17 x 43, not Frobenius) | 35,088 | **70,176** | 68,544 (SL(2,17) x Z7) | build_haar2 + apsp |
| (5,12) | Z8969 x\|_205 Z59 | 529,171 | **1,058,342** | 1,041,768 (PSL(2,53) x Z7) | build_haar2 |

Also valid (smaller, in the order found): (4,11) 28,918 (Z761 x| Z19), 26,640 (SL(2,5) x (Z37 x| Z3)), 29,470
(Z421 x| Z35), 28,938 ((Z7 x| Z3) x (Z53 x| Z13)); (5,11) 301,200 (SL(2,5) x (Z251 x| Z5)), 306,182 (Z5279 x| Z29), 310,498
(Z8171 x| Z19), 310,718 (Z3613 x| Z43); (6,11) 2,095,758 (Z16633 x| Z63), 2,098,038 ((Z67 x| Z3) x (Z307 x| Z17)),
2,100,126 ((Z7 x| Z3) x (Z1613 x| Z31)), 2,112,114 (Z20707 x| Z51); (4,12) 68,906 (Z263 x| Z131), 69,104 (Z617 x| Z56), 69,254
(Z1117 x| Z31), 70,038 (Z1297 x| Z27); (5,12) 1,045,054 (Z9859 x| Z53), 1,047,942 (Z8317 x| Z63), 1,050,906 (Z10303 x| Z51),
1,056,886 (Z8663 x| Z61). Solutions in
research/frontier/sols/ (names d<Δ>D<D>_meta_* and _prod_*, suffix b<round><card>), check logs in
research/frontier/runs/cloudcheck/<stem>.check.txt.

In size-law terms (mu = N exp(-W/N), SIZE_LAW.md) the (4,11) graph sits at mu 44 and the 28,918 one at mu 31.6, where
SL/PSL groups stall near mu 8-15; at (5,11) mu 20, (4,12) mu 18, (5,12) mu 14, (6,11) mu 11, about where SL/PSL sit. So
the advantage is large at Δ = 4 and shrinks as the cells grow.

## Why (measurements and proofs from the squad)

- r2/h13 (NOTE.md), Δ = 4, 30 random S per group: the median number of uncovered elements at radius 10 is 1.1x the
  size-law mu for Z761 x| Z19 and 1.6x for Z1093 x| Z13, but 4.3x for SL(2,23) and 5.2x for SL(2,13) x Z7. The loss is
  in the middle levels: at radius 8 the Frobenius balls reach 0.99-1.00 of the independent-words model, SL(2,small p)
  balls 0.89-0.92 (short relations make words collide). So at small N the Frobenius groups behave like random groups
  and small SL(2,p) groups do not. Involution and central holes were not the cause in this measurement.
- k matters: k = 3 collapses (1 + r + r^2 = 0 in Z_p, ball at radius 8 only 0.15 of the model), k = 7 is mildly bad,
  k = 13-63 behave like random (h13; h17: at (5,11) median holes 434 for k = 7 against 35 for k = 19).
- r2/h17 (NOTE.md): no involutions, trivial centre (proof), so the odd-D clumps of ODD_D_HOLES.md never apply; the
  C_k-coordinate of a word is a walk on Z_k whose distribution is |phi_t|^(2h) in Fourier terms; S needs at least 3
  distinct C_k labels (Cauchy-Davenport; exhaustive at (4,11), k = 19); balanced labels predict fewer holes. Turning the
  balance into a search constraint (r3/i13) lowered the mean best cost (6.0 vs 8.4 at (5,11)) but did not change the
  solve rate in 5 seeds.
- At even D the Frobenius groups also raised (4,12) and (5,12), and k may be even there (involutions do not matter);
  r3/i16 found no difference between PSL(2,101) and a Frobenius group at (5,12) in random-S statistics.

## What did not work

Automorphism orbits on Frobenius groups (scaling a -> u a puts each orbit in one coset and degenerates, r2/h10;
conjugation orbits, r1/g16, r2/h01); F_q x| C_k with q = p^3 (r1/g04, 10x worse); 2-dimensional kernels Z_p^2 x| Z_k
(r2/h16, r3/i15); composite k at equal N (r3/i15); SL(2,q) x Frobenius beyond (5,11) (r2/h05, h07); cubic cells (exh3,
best cost 84-548, r2/h11); (7,11) and above: near misses at cost 2 (Z90281 x| Z61 at N = 5.5M) but evaluations are
slow for cards (r3/i09, i14, i16).

## Limits and next steps

- haar_gen3 needs a cyclic subgroup of order 2..63 for its fast coset layout; for Z_p x| Z_k that means k <= 63 or k
  with a small divisor. k > 63 prime runs ~50 evaluations/s at N ~ 35k.
- Solve rates near the limit are ~1 in 5 seeds. haar_gen3s (r4/j14, research/squads/beyond11b/tools/haar_gen3s.c) adds
  SAVEBEST/START; haar_gen3t (r5/k13, tools/haar_gen3t.c) adds full-length targeted moves (TFULL=1). Several raises came from
  resumed chains, but the cost-1/2 states are mostly true local minima: at (4,12) an exhaustive scan of all 105,609 single
  generator swaps of a cost-1 state of Z677 x| Z52 finds no cost 0 (r6/l01).
- At odd D the holes of an odd-order group come in inverse pairs on one side (n_h(x) = n_h(x^-1), r1/g15 Theorem 1), so
  the cost is even; measured in r5/k14 and r6/l07.
- The bigger D = 11 cells (Δ >= 8) use SL(2,p) x Z_n at N >= 2e7. Whether Frobenius groups help there is open: it would
  need haar_big-style 64-bit layouts for meta groups and a low-memory checker that knows them (haarcheck_gen does not).
