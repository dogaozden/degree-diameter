# w13 NOTES (handsoff-49 round 2): the cost-4 wall at n = 4,992

Start: 2026-10-31 23:34 UTC. Planned end: 01:35 UTC (2 hours). Card: cards.md, "## w13".

## Setup
- meta.py: numpy multiplication tables for Z_m x|_r Z_k (same convention as groups.py), inverses, set products.
- hc.py: annealing on S (|S| = 4, e in S). cost = |G \ (S^-1 S)^4| + |G \ (S S^-1)^4| (A-root and B-root far elements;
  0 iff diameter <= 9). Reproduces the cost-4 floor of meta 104 24 7 in 40 s (seed 2).
- tabu.c, mh2_0/mh2_1 bases, screen_lift.sh: copies of w5's 2+2 lift tabu (TABU=1).

## Step 1 (analysis) findings so far
- Haar H(G,S) has diameter <= 9 iff (S^-1 S)^4 = G. Write T = S^-1 S = {e} + {x^{+-1}: x in a, b, c, a^-1 b, a^-1 c, b^-1 c}
  for S = {e,a,b,c}, so this is a Cayley-graph radius-4 covering condition with 6 generators.
- meta 104 24 7 (N = 2496): the best found S has A-side far set {z} and B-side far set {z, u, u^-1} with z = (52,0),
  the central involution (cost 1 + 3 = 4).
- Frequency of each element in (S^-1 S)^4 over 20,000 random S: every element is reached in >= 47% of samples. The
  rarely reached ones are exactly 13*Z_104 (cyclic of order 8, inverted by r = 7 = -1 mod 8) elements of odd index and
  its involution (52,0), with j in {0,12}. (0,12) is central too (7^12 = 1 mod 104). So the obstruction lives in the
  2-part: the central 2-elements of order 2 and 8. No single S reaches all of them at once.
- Odd-order groups have no involution, so the central-involution obstruction is absent there.
- Consequence: odd-order metacyclic groups are the natural place to look for cost 0 at orders 1243..1300 (2+2 lifts),
  829..900 (3+3) and 623..700 (4+4). Screening of the 21 odd meta groups of order 1243..1300 (mh2_1, 4 s):
  best 8 (meta:139:9:42), then 14 (23:55:2), 16 (115:11:6, 61:21:13).

## Update (lift analysis, 23:50)
- deep_odd_mh2.tsv (25 s, seed 2): the odd groups stay at 12-20; the 4 s seed-1 values (8, 14, 16) were not floors.
- lift_freq.py (mh2_1 over meta 13 96 5, 60 random voltage sets): the rarely reached side-A elements are (0, j) with
  j a multiple of 8 in Z_96 (the subgroup of order 12 in G/G' = Z_96). So the 2+2 lift obstruction also sits in the
  abelianisation, on small-order elements. Haar analysis (above) puts it in the 2-part as well.
- Full screen running in background: screen_all_mh2.tsv, all 764 metacyclic groups of order 1243..1300 (odd and even),
  mh2_1, 2 s each (about 30 min).
