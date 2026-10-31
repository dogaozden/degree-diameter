# c12 notes (mixed-orbit coset graphs with mcos, beyond 1|2,2)

Goal: bipartite max degree 6, diameter 5, n > 684. Card: research/squads/handsoff-65/cards.md (c12).

## Setup
- Tables: read-only from ../c5/groups (sg_<order>_<i>.txt). Scripts in this folder:
  - scan12.sh TYPE SECS RANDCOMB DEADLINE ORDER...  (all non-abelian groups of the orders; log scan/<TAG>.tsv)
  - sieve12.sh TYPE SECS RANDCOMB DEADLINE GROUP...  (explicit groups like 348_6; log scan/sieve.tsv)
  - logs: scan/sv.<TAG>.sg_<id>.log, best graphs: scan/sv.<TAG>.sg_<id>.best.edges
- Calibration: TYPE 1|1 on SmallGroup(342,12): SEED 2 and SEED 3 both find cost 0 (the 684 Haar graph) in 30 s.
  SEED 1 stalls at 4 in 20 s. So the annealer is fine but needs luck or a few seeds.

## Feasibility (mcos model: full double cosets only)
- Stabiliser orders s must divide 6 (a block contributes s to each vertex degree), and the two sides need equal
  sum 1/s = c. For n = 2|G| (c = 1) the feasible side partitions are [1], [2,2], [3,3,3], [2,3,6], [2,6,6,6],
  [3,3,6,6], [3,6,6,6,6], [6,6,6,6,6,6]. So 1|4,4,2 and 1|4,4,4,4 (in the card) are infeasible in mcos (4 does not
  divide 6): not tried.

## Sieve (3 s x 2 random class combinations, groups 348_6 348_5 350_1 360_119 366_2 352_4; cost = mcos violations)
- 1|2,2 (c5, 1.5 s x 3): 18 (348_6, 360_119), 22 (348_5), so the best family for cost so far.
- 1|3,3,3: 366_2 -> 21 (c5 60 s/combo: 7); 360_119 126; 348_* 1305 (disconnected-looking local minima, never below).
- 2,2|2,2: 348_5 24, 348_6 60, 350_1 58, 352_4 151, 360_119 86. Default split is impossible on 366_2 (prints 1<<30).
- 1|2,3,6: 360_119 40, 348_6 301, 366_2 275.
- 1|3,3,6,6: 360_119 57, 366_2 85, 348_6 1587.
- 2,2|3,3,3: 366_2 856, 360_119 230.  2,2|2,3,6: 348_5 338, 348_6 420, 360_119 395.
- 3,3,3|2,3,6: 366_2 510, 360_119 1349.  2,3,6|2,3,6: 360_119 237.  3,3,3|3,3,3: 366_2 1464, 360_119 1647.
- The stabiliser-order-6 types (1|6^6, 1|3,6^4, 1|2,6,6,6, 2,2|6^4, 2,2|2,6,6,6) cost 380..2300 on these groups: dead.
- Conclusion of the sieve: types with stabilisers 2 and 3 only are the competitive ones; 1|3,3,3 and 1|2,2 lead.
