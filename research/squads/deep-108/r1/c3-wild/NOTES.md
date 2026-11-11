# c3-wild (squad round 1, deep-108): notes

Card: a family none of c1 (A5 x PSL(2,59)) or c2 (PSL(2,181) x Z2) or the listed tried families covers. Target: degree 10,
more than 1,176,480 vertices, diameter 8. Time box about 90 minutes. Verdict: both new families I could evaluate are
clearly worse than K (no claim, no C = 0).

## Constraint facts (checked)
- Bi-coset degrees: A-degree = |D|/|R| and B-degree = |D|/|L| for D a union of double cosets L z R. Both equal 10 forces
  |L| = |R|. So "|L| != |R| with max degree 10" is impossible for a regular pair, and a B side of degree 5 reaches at most
  about 480,000 B-vertices within radius 7 (count 10 + 360 + 12,960 + 466,560), far below the 1.2M needed. Dead.
- Orbit model used by the coordinator: a B-orbit of size s is missed with probability exp(-lambda*s/|L|). The number of
  B-orbits is N/|L|, so the expected regular misses are mu = (N/|L|) exp(-lambda). Larger |L| at fixed N means fewer
  independent orbit events. Special orbits (stabiliser of order k > 1 in L) have P(miss) = exp(-lambda*s/|L|).
- A central element in L fixes every B-coset, so every B-orbit is special. Any twist that puts an element of L into the
  centre is useless. A central Z_m factor in G is the danger zone: see below.

## Family 1: PGL(2,229), L = R = D10 (order 20), one double coset with |L ∩ zLz^-1| = 2 (degree 10). Result: negative
- Idea: |L| = 20 with N = 12,008,760/20 = 600,438 per side, the same N as K. Orbit model: regular misses mu = 29,953 e^-9 = 3.6
  (K: 7.7). Special burden from the census of L-orbits on B-cosets (lambda = 9.0, P(miss) = exp(-9 s/20)):
  c1:1, c2:11, c5:1, c10:135 gives E_s = 0.64 + 11*0.41 + 0.11 + 135*0.011 = 6.7 (K: 3.5). Model total 10.3 against K's 11.2,
  so on paper it is not worse. Only 135 members (the c10 double cosets) exist, so the family is small enough to finish.
- Generators (script `d10gens.py 229 5`): c = (1,96,178,102) of order 10, t = (1,29,26,228) an involution inverting c.
- Census (`cq2 229 0 1 2 1 96 178 102 0 1 29 26 228 0 0 info`): c1:1 c2:11 c5:1 c10:135 c20:29953 (double cosets R g L by
  #R-cosets). Members are the 135 double cosets with 10 R-cosets.
- Exhaustive (`cq2c 229 0 1 2 1 96 178 102 0 1 29 26 228 0 0 listc 10`, output `pgl229_D10_c10.tsv`): all 135 connected
  (uBA small), min C = 704 (z = 1 20 44 194 0), p10 1094, median 2268, max 703,245.
  Uncovered B are about 700 to 2300, i.e. 35 to 115 orbits of 20. The model predicted about 3.6 + 6.7 orbits, so the
  misses are correlated (non-regular double coset, the same effect as the K tax) and 10 to 30 times larger than the model.

## Family 2: twisted C5 pairs, |L| = |R| = 5, union of two regular double cosets (degree 10). Result: negative
- Idea: L = <(x,1)>, R = <(y,z)> with x, y of order 5 in PSL(2,q), z of order 5 in Z_m. Every L-orbit on B-cosets is regular
  (census `c5:119040` for PSL(2,31) x Z200), so E_s = 0 by construction. The family has about 10^9 members (pairs of
  regular double cosets), which is the one place where it beats K on counting. Orbit model: mu = (N/5) e^-9 = 14.
- Measured:
  - PSL(2,31) x Z200 (|G| = 2,976,000, N = 595,200). `sample` 60 members (seed 11): none connected in the sense uBA < 10,000.
    Typical uBA = 476K, reach within radius 7 is about 0.2 N. `prof` on one member: level sizes 1,10,90,765,6185,37235,85176,
    80625,42464 (tree 1,10,90,810,7290,65610,590490,5314410,...). The PSL projection of the walk group is all of PSL(2,31)
    (checked with `pslproj.py`), and the cost barely depends on the residues (residue differences 1, 2, 3 give the same
    uBA), so the damage comes from the central Z200 factor, not from the PSL part.
  - PSL(2,59) x Z30 (|G| = 3,079,800, N = 615,960; x = 4 54 7 21, y = 19 7 2 7 with residue 6; file
    `psl59xZ30_sample60.txt`): 21 of 60 members connected. Connected C: min 2564, median 3676, max 8382. The disconnected
    ones have uBA = N/2, 2N/3, 5N/6, which is consistent with a component count set by the residues (I did not prove
    the gcd rule; it fits these values).
  - K has median about 340 and min 4, so this family is about 10 times worse in median.
- Reading: the Z factor is central, so walks commute in the residue coordinate and the balls collide. The B-ball saturates
  well below the tree count. A non-abelian complement (for example A5 x PSL(2,q) with |G| about 3.0M and |L| = 5) would be
  needed to test this idea properly. That group is not in cq2/cq3 and I did not write it.

## Tools and validation
- `cq2c.c` = copy of research/squads/deep-108/cq/cq2.c plus one new mode, `listc SZ`: for every double coset L g R (over
  TLR) with SZ R-cosets, it prints the exact costs (uBA, uAA, uBB) for that single-coset member. Built with
  `gcc -O2 -o cq2c cq2c.c -lm`.
- Validated on K with cq2c and the original cq2: `229 1 1 2 1 1 1 27 0 1 0 26 228 0 0 member 1 1 20 220 50 0` gives
  uBA 4, uAA 0, uBB 0 (both binaries). NOTE: the card's K string had one extra "0" before `member`, which gives "unknown
  mode"; the correct string has NR = 0 and then "member", as above.
- `d10gens.py q seed`: finds D10 generators in PGL(2,q). `pslproj.py p gens...`: order of the PSL projection of the walk group.

## What is worth more CPU (my judgment)
- The |L| = 20 PGL idea is cheap and the census numbers are on-model, but the correlated misses for i = 2 members kill it.
  If the lab wants more on this idea, the next test is PGL(2,q) D10 or D20 with i = 2 for other primes q with
  |PGL(2,q)| near 12M, and L != R, to see whether the tax depends on the group. The exhaustive run is seconds.
- The twisted C5 idea needs a non-abelian complement in place of Z_m. Not tried.
