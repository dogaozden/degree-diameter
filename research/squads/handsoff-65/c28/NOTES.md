# c28 notes (card: exact settlement of 1,6|1,6 on SmallGroup(294,11) and (294,12))

## Status 20:48 UTC
Not settled globally. What is settled is the LOCAL neighbourhood of the known cost-2 / cost-4 states (exhaustive,
exact cost via the t18 cost function; costs are counts of (representative, vertex) pairs at distance > 5 over the
four orbit representatives, as in t18/mcos).

## Model and parameters (checked)
- G = SmallGroup(294,11) = (C7 x C7) : C6, |Aut(G)| = 1764 (GAP), 49 cyclic subgroups of order 6, element orders
  1:1, 2:7, 3:98, 6:98, 7:48, 14:42.
- Type 1,6|1,6, N = 5,1,1,0: parameters S = 5 group elements (A0-B0 edges x ~ xs), G01 = g1 (A0-B1 block, a left coset
  g1K), G10 = g2 (A1-B0 block, a right coset Hg2), and the cyclic subgroups H (A1 = G/H) and K (B1 = G/K), order 6.
  That is 7 element slots plus 2 subgroup choices.
- Normalisation: S -> Sc with G10 -> G10 c is an isomorphism (relabel B0 by y -> yc; the B1 block is untouched).
  So one may take e in S, but then G10 ranges over all 49 cosets, so this does not shrink the count of configurations.
- Exact-search size, for scale: 49 x 49 x 49 x 49 choices of (H,K,g1,g2) times C(294,5) = 1.8e10 subsets S is about
  1e17 raw configurations. Dividing by |Aut| = 1764 and by about 59 for the e-in-S normalisation leaves about 1e12
  cost evaluations (about 2e7 CPU seconds at 20 us each). A plain orderly enumeration is out of reach in this session. No SAT or ILP
  solver is installed (no pysat, ortools, z3, pulp, minisat, cadical, kissat).
- Necessary conditions found (for the record): the A1 representative a = H reaches the A1 vertex cHg2 (distance 4) only
  through B0 vertices of H g2 S^-1 S, so H g2 S^-1 S must meet every block c H g2 (49 blocks of 6). Similar for B1.
  These are monotone in S, so they give no pruning in an ordered DFS without an upper bound.

## Tool: ex2.c (c28), built from c18/t18.c (cost function unchanged)
- `./ex2 TABLE 6 5,1,1,0 INIT STAGE OUTPREFIX`, env TLIM (seconds), HSTART (first H index for STAGE hub).
- STAGE pairs: all changes of two of the 7 element slots (S, G01, G10) to any element, H and K fixed.
  1.8e6 evaluations, about 140 s on the loaded machine.
- STAGE hub: every (H,K) pair (49 x 49) with every single-slot change (2058 values), 4.9e6 evaluations, about 370 s
  (run as HSTART=0 TLIM=240 and HSTART=31 TLIM=240, together complete).

## Results (exact, local)
- Calibration: pairs from cost2_294_11.init (H 155, K 80, cost 2): 1,815,156 evaluations, best 2, histogram of costs
  0..7 = 0 0 118 0 0 2 0 0. The 2-change neighbourhood contains 118 cost-2 states (the base included), so the
  search finds the known cost-2 states as expected.
- 294_11, hub stage, cost-2 state: all (H,K) pairs with one slot change: 4,961,000 evaluations in two runs, best 2,
  histogram 0 0 593 0 (costs 0, 1, 2, 3 = 0, 0, 593, 0). No cost 0 or 1 state exists within one change of the slots
  under any (H,K).
- 294_12 (cost-4 state from c18/t294_12.edges.par, H 150, K 80): 2-change neighbourhood, 1,815,156 evaluations, best 4,
  histogram 0 0 0 0 116 (no cost 2 or 3 state within two changes).
- 294_12 hub stage (all 2401 (H,K) pairs with one slot change, 4,945,374 evaluations in two runs): best 4, no cost
  0..3 state.
- Second 294_11 cost-2 state (cost2b, H 158, K 118): 2-change neighbourhood, best 2, histogram 0 0 118 0 0 2 (same
  shape as the first state).
- Third cost-2 state, found by the hub stage (hub2.init: S as cost2, G01 245, G10 31, H 156, K 80): 2-change
  neighbourhood, histogram 0 0 118 0 0 2 0 0, best 2. The three cost-2 states give the same histogram, which suggests
  one family (isomorphism not checked).
- Cost-5 states of 294_11 (c18 s40: H 116, K 81; s99: H 78, K 84; s300: H 29, K 193), 2-change neighbourhoods:
  s40 best 2 (2 states at cost 2), s99 best 2 (2 states), s300 best 5 (no state below 5).
- No cost-0 state found anywhere. No cost-1 state in any neighbourhood searched. Nothing above 684 with cost 0.

## Next
- Possible: a 3-change search with a valid prune (none found in this session); a covering prune for the orderly search.
- A full 3-change neighbourhood is C(7,3) * 294^3 = 8.9e8 evaluations, too many without a better cost bound.
- An exact answer for 294_11 needs an orderly enumeration with a covering prune (as shared/haarex3.c does for Haar
  graphs); the hub blocks add paths that the Haar prune does not model, so this was not written in this session.
