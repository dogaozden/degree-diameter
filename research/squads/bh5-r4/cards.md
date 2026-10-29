# bh5-r4 cards (read COMMON.md first)

c1 (7,5) coset graphs with h = 2 (vertices N = |G|): all SmallGroups of order 1176 and 1200 that are NOT solvable
   (GAP: Filtered([1..NrSmallGroups(n)], i -> not IsSolvable(SmallGroup(n, i)))), then solvable groups of orders
   1160, 1164, 1168, 1180, 1188, 1196 (few groups each). Use run_group2.sh with h=2, Δ=7, SA_SECS 60. Report the best
   cost per group, and for the best three say whether they are Haar (COMMON.md check). Known: A5 x C20 gives 30.
c2 (5,5) 3+3 record-type base research/beyond-haar-d5/b6/b33_9.txt over the non-abelian groups of order 60 other than
   SmallGroup(60,3) (already running): groups/sg_60_<i>.txt for i in 1, 2, 5, 6, 7, 8, 9, 10, 11, 12 (skip the
   abelian ones: check groups/sg_60_<i>.name). First a 20 s vl screen of each (D=5, no SWAP), then basin/run2.sh on
   the best two with SECS 40, K2MAX 6, K3MAX 4, about 25 runs each. TAG names b6_9_g<i>_r4.
