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

## Tabu variant (mtabu.c, built as mtabu; mtabu2 adds K2=1 exhaustive two-move polish)
- mtabu.c = shared/mcos.c with the SA loop replaced by full-neighbourhood tabu (every single double-coset swap is
  evaluated each step, best non-tabu move taken, tenure TT (default 12) + random 0..TT, aspiration if it beats the
  best of the run, restart from the run's best with KICK random swaps after STAG (3000) non-improving steps).
  Same env as mcos (TYPE, CLS, RANDCOMB, SECS, SEED, EDGES, VERB). Usage: `timeout 300 nice -n 10 ./mtabu GROUPFILE`.
- Calibration: 1|1 on SmallGroup(342,12) reaches cost 0 (684 Haar graph) in 2.4 s (SA needs 15-30 s and seeds).
- Speed: ~9k cost evaluations/s (the SA did ~38k/s but needs far more evaluations).
- Costs are not much better than SA for the hard cases; floors are reproducible:

## Results (tabu unless noted; bad = check.sh far pairs)
- 1|3,3,3 SmallGroup(366,2) C2x(C61:C3), n=732: cost 7 (bad 915) for combos (0,1,1) and (1,1,1) at every seed
  tried (SA c5: 7; tabu 40-120 s, TT 5/20, STAG 200/500). Combo (0,0,1) 11, (0,0,0) 11.
  Exhaustive two-move neighbourhood (518k pairs, K2=1) of the cost-7 state: no improvement, so it is a strict
  2-move local minimum. Far pairs of the cost-7 graph (analyze_bad.py): A-A 732 (two whole G-orbits of pairs at
  distance 6), B1-B3 122, B2-B2 61. The A side is a Cayley-type 2-step problem: T^2 must cover the group.
  Saved: deep/t366_2_rc.edges (bad 915). Scoreboard line added at 18:20.
- 1|2,2 SmallGroup(348,5) n=696: cost 8 (bad 957) in 8 s (seed 1, file scan/1_2-2.sg_348_5.best.edges), but
  seeds 11-16 at 12 s give 8,13,13,13,15,17. SA (c5) had 22. 360_119 (n=720) tabu 17 (SA 18).
- 1|3,3,3 363_2 (n=726): cost 10 (bad 1089), deep/t363_2.edges. 399_4 (n=798): cost 18 (bad 2527).
  372_11 (n=744): cost 14 (bad 1612). 372_1 21, 378_17 26 at 8 s.
- 2,2|2,2 348_5 tabu 12 s: 21 (SA 24). 1|2,3,6 360_119: 37. 1|3,3,6,6 360_119: 153 (SA 57 -> tabu worse).
- 3,3,3|3,3,3 on 351_12, 363_2, 366_2, 375_6: cost 1452-2204 (dead).

## Scans (tabu, 8 s x 1 random class combo per group; log scan/1_3-3-3.tsv, scan/1_2-2.tsv)
- 1|3,3,3 over all non-abelian groups of orders 348,350,354,356,358,362,364,366,370,372,374,376,378,380 (119 groups)
  and over the odd orders 345,351,357,363,369,375,381,387,393,399 (groups12/, generated with gap_tables.g):
  best 366_2 13, 363_2 14, 399_4 18, 372_11 20, 372_1 21, 372_2 24, 378_17 26, 381_1 26.
- 1|2,2 over 348,350,364,366,370,372,374,376 (29 groups): best 348_5 8, 348_6 17, 350_7 18, 350_1 21.

## Conclusions so far
- No cost-0 graph; best n>684 is cost 7 / 915 far pairs at n=732 (same as c5). Floors are reproducible across seeds,
  combos and both annealers; a 2-move exhaustive check does not break the floor.
- Types with stabiliser orders 6 (1|6^6, 1|3,6^4, 1|2,6,6,6, 2,2|6^4, 2,2|2,6,6,6) and 3,3,3|3,3,3 are far worse
  (costs 300 to 2300), so the mcos family looks exhausted for c=1, |G| in 343..400 apart from 1|3,3,3 and 1|2,2.
