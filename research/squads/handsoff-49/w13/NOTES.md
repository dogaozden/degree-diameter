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

## Update 00:25: the wall, what I measured, and what did not work
- Haar criterion (exact): H(G,S) has diameter <= 9 iff (S^-1 S)^4 = G (same-side pairs; opposite side is implied).
  cost (haar_tab convention, D = 9) = |G \ (S^-1S)^4| + |G \ (SS^-1)^4|.
- Obstruction for meta 104 24 7 (N = 2496): the central involution z = (52,0) (the only one of the 3 involutions that is
  central in G; (0,12) and (52,12) are central too, but are always reached).
  * 4,098 annealed states with cost <= 6: z is far on at least one side in 100% of them; the other two central
    involutions are never far.
  * Random S (20,000): z is reached on side A exactly when it is reached on side B (the two sides share the status).
  * Forcing z reached (penalty, 60 s anneal): min cost 8. Free annealing (40 s): min cost 4 with z far on both sides.
  * Same test on meta 208 12 3 (N = 2496, central involution (104,0)): forcing z reached gives min cost 12 (40 s).
  So for the two cost-4 Haar families, reaching the central involution costs more than the 4 that the optimum pays.
  Not a proof (no exhaustive argument), but both floors have the same shape.
- The central-involution explanation does not explain the whole landscape: the 325 even-order metacyclic groups of order
  2486..2600 with no central involution screened with haar_tab 2 s (nocen_screen.tsv) have floors >= 10 (best 2530 with
  meta 115 22 4, cost 10; 2500 Z_25 x| Z_100 cost 13). The 2 s screen does give 4 for 104 24 7, so it is informative.
- Lifts (2+2, base mh2_1): odd-order groups stay at 12-16 after 60 s (61:21:13, 115:11:6, Heis-type semi 5 3 x Z_17
  gave 12, 139:9:42 gave 16). Even 13 96 5 gives 4 at 50-60 s (w5). Orders 1244 and 1246 (7 groups): costs 92 to 9,500.
  3+3 odd orders 829..841 (mh3_3, 15 s): floors 28 and up. So the odd-order idea for lifts did not hold.
- Broad screen of all 764 metacyclic groups of order 1243..1300 was stopped after 35 (2 s runs are too noisy for lifts:
  13 96 5 reads 20 at 2 s and 4 at 50 s); it was not a useful use of the machine.

## Result
- Best own near miss: n = 4992, cost 4, Haar meta 104 24 7, file w13/best_haar_104_24_7_c4.edges (apsp INVALID at 9,
  4,992 far pairs, diameter 10). Rebuild: S = {0, 1214, 1499, 2305} in meta 104 24 7 (index a + 104 j), edges (g,A)-(s g,B).
- No record. Lift best (odd order, n = 5004): cost 8 (4 s), not kept.

## What I would try next
1. Groups where the central involution does not exist and the abelianisation has no small-order part, at orders 2496..2530
   with the two-root cost (the 2 s screen is cheap; 2530 and 2500 are the best so far), then 60 s on the top 5.
2. Lifts: exhaustive voltage search (exh-style) on mh2_1 over meta 13 96 5, to see whether 4 is the floor there too.

## Final notes (00:45 UTC)
- Lifts over non-metacyclic groups of order 1248..1300 (sl2 3 x cyc 52/53/54, agl1 7 x cyc 30, psl2 5 x cyc 21), mh2_1,
  8 s: costs 25 to 72. Not competitive.
- Base mh2_0 = [[3,1],[1,3]] over the 15 best order-1248 metacyclic groups of w5's screen, 8 s: best 12 (meta 208 6 121),
  then 14. Not better than mh2_1.
- Odd-order metacyclic Haar groups of order 2487..2523 (19 split groups, haar_tab 4 s): best 144. Only 2525 (101 25 5)
  is near the threshold among odd orders, and it is certified at cost 2 by w11.
- Trivial-centre metacyclic groups of order 1243..1300 as 2+2 lifts (4 s): best 16. Small centre does not help lifts.
- meta 13 96 5, 2+2 mh2_1, 300 s tabu, seed 9: cost 10. Seeds matter: w5's seeds 31/61/72 reached 4 in 50-60 s.
- Files: best_haar_104_24_7_c4.edges (n = 4992, cost 4), nocen_screen.tsv (325 no-central-involution groups, 2 s),
  centre_1243_1300.tsv (centres of the 764 groups), screen_centreless.tsv, long60_mh2.tsv, long300_mh2.tsv.

## Last runs (00:59 UTC)
- 2+2 mh2_1, 120 s tabu: meta 39 32 31 seeds 201/202/203/204 -> 4, 10, 10, 12 (the floor 4 is hit about once in four
  seeds at this length, never below 4). meta 13 96 5 seed 201 -> 10.
- Other order-1248 members of the 39 32 family, 90 s, seed 301: meta 39 32 5 -> 6, 39 32 25 -> 56, 39 32 38 -> 90,
  39 32 14 -> 218 (fam39_mh2.tsv).
- Floor summary for n = 4972..4992 (2+2 lifts, 4N = n): best 4 (order 1248, meta 39 32 31 and 13 96 5), i.e. no
  improvement on the card's wall. Haar: 4 at N = 2496 (both cost-4 families); odd Haar 2487..2523 far worse.
