# c15 notes: bi-coset |H| = |K| = 2 on the groups of orders 722..766 not yet swept by c4

Target: bipartite degree 6, diameter 5, n > 684. Card: sweep the remaining groups with diagonal class pairs (H = K),
then rerun the best ones with long anneals.

## Setup (17:46)
- Scripts copied from c4 and adapted: sweep15.sh (one group: GAP export via shared/dc2_lib.g, then dcenum SA on each
  diagonal pair), chunk15.sh (walks remain.txt from the pointer in next.txt for ~240 s, foreground only).
- done_c4.txt: 237 (order, id) groups already run by c4 (sa h2 lines, incl NOPAIRS). all_e.txt: 691 even-order groups
  of c4's task list. remain.txt: 468 groups still to do, in order of (order, id).
- ExportPairs filters H with core > 1, so central involutions (Haar graphs, already closed for 343..400) are never run.

## Commands
- one chunk: `cd c15 && timeout 300 nice -n 10 ./chunk15.sh` (SECS env sets SA seconds per pair, default 6)
- results: c15/results.txt ("sa d6 ORDER ID pair ndc=.. | best COST vertices N"); cost-0 graphs to c15/HITS/,
  cost <= 20 graphs to c15/best/.

## Progress
- 17:50: first chunk started (remain.txt lines 1..19: orders 722..728).

## Status 18:13
- Speed: the stock ExportPairs computes every (i,j) pair of involution classes (DoubleCosets for each); c15/dc2_diag.g
  (copy with `for j in [i..i]`) exports only the diagonal pairs (736,184: 10 s -> 4.7 s). sweep15.sh uses it.
- Annealing time per diagonal pair: 6 s for the first 25 groups (orders 722..728), 3 s until 18:00, 2 s since.
  The 2 s screen is noisy; any group with best <= 40 gets a 6 s or longer rerun before it counts.
- Pointer 111 of 468 (orders up to ~734). 0 cost-0 graphs so far. Best so far (screen): 20 at SmallGroup(732,10)
  (best/g732_10_p_1_1_c20.edges, bad = 3660 by check.sh), then 24 at 732,7 and 26 at 728,32.
- Scoreboard line written for the cost-20 graph.
- Note: groups with many diagonal classes (736 family) take ~5 pairs x SA; equal costs across pairs (728,38: four
  pairs all 302) suggest automorphic duplicates; not deduplicated.
