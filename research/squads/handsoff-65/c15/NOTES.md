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
- 18:42 deep15.sh 750,6 pair 1, 120 s SA: 12 (same plateau). EXHAUSTIVE dcenum on the same pair (2,898,115 unions, 2m40 real, 68 s user): min cost 12, no solution. So 750,6 p(1,1) is closed at >= 12. Exhaustive is feasible for ~3M unions (195 double cosets, 180 of contribution 2).
- 19:01 exhaustive 750,10 pair 1: min 16 (2,898,115 unions, no solution). SA at 2 s found the exact optimum on both pairs, so the screen values are likely pair optima.

## Final 19:30
- Swept all 468 remaining groups (remain_v1.txt order, then reordered: 738..766 first, 736 last). 912 result lines:
  162 groups NOPAIRS (no non-central involution class; these are the Haar cases already closed), 750 diagonal pairs
  with SA (6 s for orders 722..728, 3 s until 18:00, 2 s after). Groups with pairs: about 306.
- Best screened costs: 12 at SmallGroup(750,6) pair 1 (SA 2 s, 120 s SA, and EXHAUSTIVE: min 12 over 2,898,115
  unions, no solution); 16 at SmallGroup(750,10) and SmallGroup(750,11) pair 1 (both exhaustive: min 16);
  20 at 732,10 and 750,20; 22 at two more; then 23+.
- No cost-0 graph in the family (no HITS). Best file: c15/best/g750_6_p_1_1_c12.edges (bad = 2250 far pairs by check.sh; see
  scoreboard). Costs are 'missed vertices from the two BFS sources', so cost 12 is roughly 12..(a few thousand) far pairs.
- Lesson: the 2 s SA already reached the exact pair optimum on the three pairs checked exhaustively (750,6 / 750,10 /
  750,11), so the sweep values are reliable per pair. The family (|H| = |K| = 2, diagonal, non-central, |G| in 722..766)
  bottoms out at 12, same as the c4 result 756,74 (cost 12). Nothing reaches 0.
- Not done: exhaustive on the other top pairs (732,10; 750,20); mixed pairs (H != K); deduplication of automorphic pairs.
- No processes left. tmp/ removed.
- 19:30 exhaustive 732,10 pair 1: min 20 (1,200,211 unions, no solution). Closed at 20. tmp/ removed.
- 19:32 exhaustive 750,20 pair 1: min 20 (1,209,345 unions, no solution). Closed at 20. Final best: 12 (750,6), then 16 (750,10 and 750,11, both exhaustive-closed at 16).
