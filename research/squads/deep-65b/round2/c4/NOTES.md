# round2 card c4: order 192, groups C3 x P64 (second half, round2/c4/ids.txt)

Result: NO zero. Best cost 8 (= 8 missing elements over C1..C6) on SmallGroup(192,900) and SmallGroup(192,168).
No graph built (no zero, so nothing to score with apsp). Time used: about 49 min of the 60-min box.

## Setup
- ids: round2/c4/ids.txt (128 ids, all non-abelian; names "C3 x (...)"). Split: `tr -s ' \n' '\n' < ids.txt > all_ids.txt; split -l 20 -d -a 1 all_ids.txt chunk_` (chunk_0..chunk_6).
- Tables (tables only, no AUT), one call per chunk, from research/squads/deep-65b:
  `shared/gapw -c "ORDER:=192; IDS:=[$(paste -sd, round2/c4/chunk_K)]; OUTDIR:=\"round2/c4/tabs\";" tools/gap_fast.g`  (K = 0..6; ~14 s each)
  Result: tabs/sg_192_<id>.tab and .name for all 128 ids; each .tab has first line 192 and 193 lines in total; all 128 names say abelian=false.
  (GAP prints harmless "Syntax warning: Unbound global variable" lines from gap_fast.g; ignored.)
- Search program: shared/tabu15 (round 1's, unchanged), wrapper round2/c4/scan.sh:
  `./scan.sh SECS SEED TODO` runs tabu15 on each "192 id" line of TODO (skips runs already in raw.txt, starts no run after 85 s of the call), appends `ord id seed secs best t_best name` to raw.txt.
  Writes an edge file to edges/ only if cost 0 (none written).

## Passes (all 8 s per run, runs are time-capped by tabu15 itself)
1. `timeout 105 nice -n 15 ./scan.sh 8 1 todo.txt` (todo.txt = all 128 ids), 128 runs, about 12 calls.
2. `timeout 105 nice -n 15 ./scan.sh 8 2 todo.txt`, 128 runs.
3. Top 10 after passes 1-2 (by min cost, ties by mean): todo_top10.txt = 900, 934, 916, 168, 174, 924, 932, 912, 874, 920.
   Seeds 3..8, one seed per call: `./scan.sh 8 S todo_top10.txt` for S = 3, 4, 5, 6, 7, 8 (60 runs).

## Results
- Best per group (min over runs): best_per_group.tsv (order, id, best, mean, runs). Full per-run data: raw.txt.
- Best costs: 900 -> 8 (C3 x ((C2 x C2) : Q16); seeds 1..8: 18, 8, 16, 8, 21, 16, 8, 8).
  168 -> 8 (C3 x (C2 . ((C8 x C2) : C2) = C8 . (C4 x C2)); seeds 1..8: 11, 13, 13, 17, 13, 15, 12, 8).
  934 -> 10, 916 -> 10, 932 -> 11, 174 -> 11, 924 -> 11, 912 -> 11 (seed 2; seeds 3..8 gave 12-16), 874 -> 12, 920 -> 12.
- Distribution of per-group best (128 groups): 8 (2 groups), 10 (2), 11 (4), 12 (6), 14 (12), 15 (3), 16 (9), 17 (5), 18 (9), 19 (5), 20 (8), 21 (5), rest higher.
- Outliers that stay high in both seeds: 177 (86, 86), 926 (79, 89), 1410 (56, 58), 1424 and 1455 (38-46). The tabu seems to get stuck on these; not informative about the family.

## Caveats
- 8 s per run is ~500 tabu steps (round 1: ~65 steps/s at m = 176, and m = 192 is slower). The calibration hit (176_23, cost 0 at seed 3 in 5.75 s) needed about that much, so order 192 runs may simply be too short. A zero at 192 would need more seeds or the faster tabu (card c6); I did not run longer seeds.
- The cost-8 groups are the best in this half of the 192 list, but 8 is still far from 0.

## Scoreboard
Lines appended to round2/scoreboard.jsonl: new best 11 (192,168, seed 1), new best 8 (192,900, seed 2), and a final summary line.
