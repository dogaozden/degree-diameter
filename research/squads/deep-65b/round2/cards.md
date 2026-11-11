# deep-65b round 2 cards (Opus-written, 6 Haikus): push the split family above 704

## What happened in round 1
Card c1's tabu over (E1, E2) found a VALID graph on 704 vertices (> 684, the table value): the [[1,5],[5,1]] lift by
SmallGroup(176,23) = C11 x (C8:C2) = C11 x M16 (Opus rebuilt it from a formula and checked it with apsp: records/).
The exact search (tools/split15.c) re-found the same solution class, so search and family are calibrated.
Now the record to beat is 704 (n = 4m, so m >= 177). Note the winner's shape: a central cyclic C11 times a 2-group of
order 16. Tabu is noisy: the hit came from 1 of 5 seeds (9 s each), so more seeds per group matter more than long runs.

## Common rules (every card)
- Goal: a bipartite graph with maximum degree 6 and diameter 5 on MORE than 704 vertices.
- The family: see "Background" in research/squads/deep-65b/round1/cards.md (two 5-sets E1, E2; six conditions).
- Tabu: `research/squads/deep-65b/shared/tabu15 TAB SEED SECS [EDGES_OUT]` (round-1 c1's program; source shared/tabu15.c;
  prints one line `RES n=.. seed=.. best=COST t_best=.. E1=.. E2=..`; with EDGES_OUT it writes the graph when it reaches 0).
  Example driver: shared/scan15.sh (round 1's; copy and adapt it to your folder: it reads "order id" lines, skips done
  runs, and starts no new run after ~85 s so each call stays under 110 s).
- Group tables: research/squads/deep-65b/groups/ has orders 172-190 (except 183), 195-200 (.tab + .name). Others: export
  into YOUR folder with the fast exporter, run from research/squads/deep-65b:
  `shared/gapw -c 'ORDER:=192; IDS:=[128,129]; OUTDIR:="round2/cX/tabs";' tools/gap_fast.g` (one call per <= 20 groups
  so it stays under 110 s; about 1-3 s per group of order 192). Tables only (no AUT) are enough for tabu15.
- Checks for any cost 0: `shared/split15 TAB edges <E1 x5> <E2 x5> OUT.edges` (or tabu15's EDGES_OUT), then
  `shared/score65 OUT.edges` (bad=0) and `shared/apsp OUT.edges 6 5` (RESULT VALID). Put it on the scoreboard AT ONCE.
- Machine: 4 cores shared with 6 other workers and Opus. Single-threaded. EVERY command under 110 s
  (`timeout 105 nice -n 15 CMD`), chain short runs; no background processes, no sleep, no git, at most 1.5 GB memory.
- Work only in research/squads/deep-65b/round2/<card>/. Time box: 60 minutes. NOTES.md with exact commands and results.
- Scoreboard: research/squads/deep-65b/round2/scoreboard.jsonl, one JSON line per new best and one at the end:
  {"card": "c1", "idea": "...", "code": "...", "command": "...", "n": N, "score": COST, "valid": true|false, "next": "..."}
- Final reply to Opus: at most 5 lines (best per order, any hit with its E1/E2 and group).

## c1: order 180 (n = 720), all 33 non-abelian groups, many seeds
Round 1 gave 180_6, 180_13, 180_21 cost 6 with 1-2 short seeds; everything else at 180 had one 9 s seed. Run seeds
1..6 x 12 s on every non-abelian group of order 180 (groups/sg_180_*.name says abelian=...), then 10 more seeds on the
5 best groups. Report the best cost per group (table) and any zero.

## c2: orders 178, 182, 183, 184, 186, 188, 189, 190 (n = 712-760)
Export order 183 yourself (C61:C3 is there). Same plan as c1: seeds 1..6 x 12 s on every non-abelian group of these
orders, then 10 more seeds on the 5 best. Report best per group and any zero.

## c3: order 192 (n = 768), groups C3 x P (P non-abelian of order 64), first half
The winner is C11 x (group of order 16); the analogue at 192 is C3 x (group of order 64). The 128 ids are in
round2/c3/ids.txt. Export them (tables only), then 2 seeds x 8 s each; then 6 more seeds on the 10 best. Report the
best costs and any zero.

## c4: order 192, groups C3 x P (P non-abelian of order 64), second half
Same as c3 with round2/c4/ids.txt.

## c5: orders 195, 196, 198, 200 (n = 780-800) and the order-192 groups that are NOT C3 x P64
First all non-abelian groups of orders 195-200 with tables in groups/ (3 seeds x 8 s). Then, from order 192, pick
groups with a large centre-free part, e.g. those whose ids are not in round2/c3/ids.txt or round2/c4/ids.txt (sample
about 60 of them spread over 1..1543, skipping abelian ones), 2 seeds x 8 s. Report best per order and any zero.

## c6: make the tabu faster (code card)
shared/tabu15.c does a full neighbourhood scan per step (10 positions x m candidate elements), recomputing the six
conditions from scratch: about 65 steps/s at m = 176. Write tabu15f.c in your folder with the SAME search rule but a
faster evaluation, for example: keep the six coverage sets as COUNTS (multiplicity of each group element among the
words), so replacing one element of E1 or E2 updates only the words containing it (decrement old words, increment
new ones); or evaluate each candidate move incrementally and abort as soon as its cost exceeds the current best move.
Requirements: (1) on 20 random states, your cost equals `shared/split15 TAB cost ...`; (2) speed in steps/s vs
tabu15 on groups/sg_176_23.tab; (3) time-to-zero on sg_176_23.tab over seeds 1..10 (tabu15 hit 0 at seed 3 in 5.75 s).
If it is clearly faster, use the rest of your time on order-192 groups NOT in c3/c4's lists (ids 1..127 and others,
non-abelian), 2 seeds x 8 s, and report any zero.
