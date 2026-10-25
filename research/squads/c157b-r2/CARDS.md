# c157b-r2 cards (read COMMON.md first). Baseline SCORE n = 2,501,008.
c1 (P sets, better ILS): improve P0 and P1 (the smaller of the two counts) under the mask allow_P2: write a stronger
   ILS than dpack.c for 1-defective sets (e.g. moves that insert an element and its partner together, plateau moves that
   swap a pair for two singles, tabu, larger kicks). Score with S3, S4 unchanged.
c2 (S sets, better ILS): the same for S3 and S4 (lines, mask allow_S2), P0, P1 unchanged.
c3 (alternating): several rounds of: dpack (or your own ILS) on P0, P1 with the current mask, recompute masks, dpack on
   S3, S4, recompute masks, score. Longer runs; keep the best scored state.
c4 (fewer drops): the scorer drops about 300 elements in the first assignment round before it converges. Find out why
   (look at research/d15D7b/tm3_build.py do_assign: demands, bip_match per level; v3_drop.py) and reduce the loss: e.g.
   choose which end of an unserved pair to drop, refill after dropping (short dpack run with the exact masks), or make the
   set search avoid pairs whose partner coverage is contested (many paired elements needing the same covering line).
c5 (starts): try other starting sets for the relaxed search: the alternative 8,645-point set
   research/squads/c157b-r1/c4/best_P.txt, images of RH / RL under other collineations (shared/gperm.py), Pfree_unmasked
   filtered to the mask (drop one end of every pair with an unallowed end). Run dpack from each, score, keep the best.
c6 (wildcard): an idea none of c1-c5 uses to raise the score, e.g. making the four sets share structure so that their
   coverage interlocks (the P masks come from S3 u S4, the S masks from P0 u P1), or exploiting that elements in both P0
   and P1 have two free slots at level 2; must be scored with the scorer.
