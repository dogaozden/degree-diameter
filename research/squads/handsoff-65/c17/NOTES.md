# c17 notes (tabu search for multi-orbit coset graphs; card c17, round 2)

Goal: bipartite max degree 6, diameter 5, n > 684. Cost = mcos cost (orbit representative x vertex violations);
bad = far pairs from `../shared/score65` (for the scoreboard).

## Tools in c17/
- `mtabu17.c` (binary `mtabu17`): shared/mcos.c with the SA loop replaced by a full-neighbourhood tabu search
  (every single double-coset swap evaluated each step, best non-tabu move, tenure TT + rand(0..TT), aspiration,
  kick from the best state after STAG non-improving steps with KICK random swaps).
  Env as mcos: TYPE, CLS, RANDCOMB, N (block degree split, needed for c != 1 types), SECS, SEED, EDGES, VERB.
  Extra: TT (10), STAG (300), KICK (3). With LNS=1: block-LNS (re-optimise one block exhaustively or sampled,
  NCAP 20000, PASS 2) - tested, worse than tabu on 366_2 (22 vs 7-11).
  Usage: `TYPE='3,3|3,3' N='1,1,1,1' RANDCOMB=3 SECS=60 SEED=5 EDGES=out.edges nice -n 10 ./mtabu17 GROUPFILE`.
- `tables17.g`: GAP multiplication tables (same format as shared/gap_tables.g, faster lookup).
- `screen17.sh TYPE N SECS NCOMB ORDER:ID ...`: builds each table, runs mtabu17, deletes the table, appends
  screen17.tsv.  `feas_all.txt`: groups of orders 516..600 (3 | order) with a NON-normal element of order 3
  (needed for full double cosets; if all order-3 subgroups are normal, every block is short: "split impossible").
- `rndbip.py N SEED OUT`: random 6-regular simple bipartite graph on 2N vertices (calibration).

## Calibration
- TYPE 1|1 on SmallGroup(342,12) (684 Haar graph): cost 0 in 3 s, check.sh says VALID d=6 D=5 n=684.
- Random 6-regular bipartite graphs on 732 vertices (rndbip.py): bad = 14858..15248. So the coset families
  (bad 500..2000) are far better than random, and the Haar graph is far better still.

## Results (tabu, cost = mcos cost; bad = score65)
- 1|3,3,3 SmallGroup(366,2), n=732: cost 7 (bad 915) for combo 0,1,1 at seeds 1, 21, 24; cost 11 for others.
  Same floor as c5/c12. Other combos 11.  SmallGroup(372,2) n=744: 24 for all combos (floor). 363_2 and 399_4,
  372_11 are worse (see c12).
- 1|2,2 SmallGroup(348,6) n=696: cost 16 in 40 s (c5 SA 18; c12 tabu finds 348_5 at 8).
- NEW regime (not covered by c5/c12, which only used c = 1): types with c = 2/3, n = 4|G|/3, e.g. TYPE 3,3|3,3
  with N=1,1,1,1 (each block one double coset pair, row and column sums 2). Screen (6 s x 2 combos) on order
  516..600 groups with a non-normal order-3 subgroup:
    * SmallGroup(546,15) = C2 x (C7:(C13:C3)), n=728: cost 6, bad 546 (t728_546_15.edges). BEST so far.
    * SmallGroup(546,9) = C7:(C2 x (C13:C3)): cost 10.  546_16: 12.  546_5: 16.
    * SmallGroup(516,11) = (C2xC2):(C43:C3), n=688: cost 12, bad 1032 (t688_516_11.edges), all 4 combos 12.
    * SmallGroup(525,5) = (C5xC5):(C7:C3), n=700: cost 14.
    * SmallGroup(558,8) 54, 558_10 30, 546_5 16; order 528 groups with C11 factor: 1600+ (dead);
      order 522 and 516 groups with normal order-3 subgroups: "split impossible".

## Scoreboard
- 19:02 c17 3,3|3,3 SmallGroup(546,15): n=728, bad=546 (cost 6).

## Next (planned)
- Deep tabu on 546_15 (more seeds, TT/STAG variants, all 4 combos) and 546_9.
- Screen the rest of orders 567, 582, 585, 588, 594, 600 with the same type (short screens), then deep runs.
- Try the other c = 2/3 types on 546_15 (2,6|2,6, 2,6|3,3, 3,3|3,6,6 ... with N chosen by hand).
