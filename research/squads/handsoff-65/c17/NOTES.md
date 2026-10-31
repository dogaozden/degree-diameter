# c17 notes (tabu search for multi-orbit coset graphs; card c17, round 2)

Goal: bipartite max degree 6, diameter 5, n > 684. Cost = mcos cost (orbit representative x violating vertex);
bad = far unordered pairs from `../shared/score65` (the number reported to the scoreboard).

## Tools in c17/
- `mtabu17.c` (binary `mtabu17`): shared/mcos.c with the SA loop replaced by a full-neighbourhood tabu search
  (every single double-coset swap evaluated each step, best non-tabu move, tenure TT + rand(0..TT), aspiration,
  kick from the run's best state after STAG non-improving steps with KICK random swaps).
  Env as mcos: TYPE, CLS, RANDCOMB, N (block degree split; needed for c != 1 types), SECS, SEED, EDGES, VERB.
  Extra env: TT (10), STAG (300), KICK (3). LNS=1 switches to block-LNS (one block re-optimised exhaustively or
  by NCAP=20000 samples per move, PASS, KICK): tested on 1|3,3,3 366_2, worse (22 vs 7..11), not pursued.
  Usage: `TYPE='3,3|3,3' N='1,1,1,1' RANDCOMB=3 SECS=60 SEED=5 EDGES=out.edges nice -n 10 ./mtabu17 GROUPFILE`.
- `tables17.g`: GAP multiplication tables (same output format as shared/gap_tables.g).
  Usage: `gap -q -c 'ORDER:=546; OUTDIR:="groups17"; IDS:=[15];' tables17.g`.
- `screen17.sh TYPE N SECS NCOMB ORDER:ID ...`: builds each table, runs mtabu17, deletes the table, appends
  `screen17.tsv` (empty best = every combo "split impossible").
- `feas_all.txt`: groups of orders 516..600 with 3 | order that have a NON-normal element of order 3 (needed for
  full double cosets). Made by `feas17.g`.
- `farkinds.py EDGES SIZES`: far pairs grouped by orbit block (SIZES = orbit sizes in vertex order).
- `rndbip.py N SEED OUT`: random 6-regular simple bipartite graph on 2N vertices (calibration).

## Calibration
- TYPE 1|1 on SmallGroup(342,12) (the 684 Haar graph): cost 0 in 3 s; check.sh: VALID d=6 D=5 n=684.
- Random 6-regular bipartite graphs on 732 vertices (rndbip.py): bad 14858..15248. So the coset families
  (bad 500..2000) are much better than random graphs; the Haar graph (684) is 0.

## Results (tabu; cost = mcos cost; bad = score65)
Old family, c = 1 (c5 and c12 already report these; same floors):
- 1|3,3,3 SmallGroup(366,2), n=732: cost 7, bad 915 (combo 0,1,1; seeds 1, 21, 24). Other combos 11.
  (t366_011.edges). Note: t366_s11.edges has cost 11 but also bad 915, so cost and bad are not monotone here.
- 1|3,3,3 SmallGroup(372,2), n=744: cost 24 in all 4 combos (floor).
- 1|2,2 SmallGroup(348,6), n=696: cost 16 (40 s).

NEW family, c = 2/3 (not covered by c5/c12, which only did c = 1): TYPE 3,3|3,3, N=1,1,1,1, n = 4|G|/3.
(Other c=2/3 types are infeasible or much worse on 546_15: 2,6|2,6 split impossible; 2,6|3,3 cost 776;
3,3|2,6 cost 781; 3,6,6|3,6,6 and 6,6,6,6|6,6,6,6 split impossible (order-6 subgroups contain the central involution
of 546_15, so no full double cosets). Any N other than 1,1,1,1 disconnects the graph.)
Screen (4 s x 1 random combo, then deeper runs), group -> best cost:
- SmallGroup(546,15) = C2 x (C7:(C13:C3)), n=728: cost 6 in ALL 9 class combinations (12 s each) and in 6 seeds of
  60 s (also with TT 30 / KICK 8). BEST: bad = 546 = 3 x 182, t728_546_15.edges. Far pairs: 91 in each of the four
  orbits (a perfect matching of each orbit) and 182 between the two B orbits (analyze with farkinds.py). A
  structural floor for this group, not a search failure.
- SmallGroup(525,5) = (C5xC5):(C7:C3), n=700: cost 8, bad 700 (d525_5.edges; screen 14).
- SmallGroup(546,9) = C7:(C2x(C13:C3)), n=728: cost 10, bad 910 (d546_9.edges).
- SmallGroup(516,11) = (C2xC2):(C43:C3), n=688: cost 12, bad 1032 (t688_516_11.edges); all 4 combos 12.
- SmallGroup(546,16): 12; (546,5): 16; (582,2) = C2 x (C97:C3), n=776: 20; (579,1) = C193:C3, n=772: 32;
  (600,115), n=800: 24; (588,11): 29; (546,10): 30; (558,10): 30 (combo-dependent, 346 for a bad combo).
- Dead: order 528 groups with a C11 factor (about 1600+), most 552/564/567/555 groups (800+), 522 and 516 groups
  whose order-3 subgroups are normal (split impossible).

## Scoreboard
- 19:02 c17 3,3|3,3 SmallGroup(546,15): n=728, bad=546 (cost 6), t728_546_15.edges.
- Nothing else beats the board (c5/c12 have 732/915 and 696/957 etc.).

## Next (if time)
- Check whether the cost-6 floor on 546_15 survives a 2-move exhaustive polish (1440 single moves, pairs ~1e6, about
  2 min at 110 us per evaluation).
- Deeper runs on 525_5 (cost 8) and the 546 family with other class combinations; c=2/3 on more groups of
  orders 517..600 with central involutions removed.

## Final additions (20:05)
- CORRECTION: for TYPE 3,3|3,3 with N=1,1,1,1 each block holds ONE double coset (n_ab = 1), and there are 60 full
  double cosets per block (not 182). The whole mcos space for a fixed class combo is therefore 60^4 = 1.3e7 graphs.
- EXHAUSTIVE (mtabu17 with FULL=0 FULLB=60, run in 6 chunks of 10 block-0 indices, about 2.7 min each): SmallGroup(546,15),
  combo CLS=0,1,0,1: the minimum mcos cost over ALL 1.3e7 configurations is 6 (no cost < 6). So for this group and
  combo the cost-6 floor is exact; t728_546_15.edges (bad 546) is an optimal member of the family for that combo.
- Also the 2-block exhaustive polish (P2B=1) and the 2-move polish (P2=1) around the cost-6 state: no improvement.
- Other combos of 546_15 gave 6 in 12-s runs (all 9 combos), so the family floor for this group is 6 in every combo
  tried; the exhaustive proof covers only combo 0,1,0,1.
- Scoreboard: no new line after 19:02 (no graph beats 546/728 among my results; 525_5 is 700/700).
- Processes: none left from c17 at 20:06. Scratch tables in groups17/ were deleted (regenerate with tables17.g).
- 20:08-20:12 partial exhaustive slices for combo 1,1,0,0 (block-0 index 0..19 of 60, i.e. 4.3e6 of 1.3e7 graphs): min 6.
- Final state 20:08: no processes from c17; files: NOTES.md, screen17.tsv, mtabu17.c (binary mtabu17), tables17.g,
  screen17.sh, farkinds.py, rndbip.py, feas17.g, feas_all.txt, edge files t728_546_15.edges (best, bad 546),
  t688_516_11.edges, d525_5.edges, d546_9.edges, t366_011.edges, cal342.edges (calibration).
