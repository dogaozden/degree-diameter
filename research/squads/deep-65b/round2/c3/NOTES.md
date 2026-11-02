# deep-65b round 2, card c3 (order 192, groups C3 x P64, first half)

Start 2026-11-01 23:55:42 UTC, 60-minute box. No zero found.

## Steps and exact commands
1. ids.txt (128 ids) split into chunk_00..06 (20 ids each; ids_lines.txt is the one-per-line form).
2. Tables (no AUT), one call per chunk, from the deep-65b folder:
   timeout 105 nice -n 15 shared/gapw -c "ORDER:=192; IDS:=[<chunk>]; OUTDIR:=\"round2/c3/tabs\";" tools/gap_fast.g
   Result: tabs/sg_192_<id>.tab and .name for all 128 ids (m = 192). All 128 names say abelian=false.
3. Search: round2/c3/scan.sh "SEEDS" 8 TODO (my driver). It runs shared/tabu15 TAB SEED 8 EDGES_OUT and starts no new
   run after 92 s of the call. Under nice and the shared load each 8 s run got about 55-60% of a core: 385-973 steps per run.
   - Phase 1 (todo1.txt = all 128 ids, seeds 1 2): 256 runs, 22 calls.
   - Phase 2: top 10 by (best, mean) over phase 1 (todo2.txt, ranking in best_ranked.txt), seeds 3..8: 60 runs.
   Raw results: raw.txt ("id seed best t_best", one line per run). res.txt has the full RES lines (E1, E2, six
   breakdown counts); line k of res.txt is run k of raw.txt. summary.txt: "id best mean nruns" per group.

## Results
- No cost 0 on any of the 128 groups (316 runs). No edge file was written (edges/ is empty).
- Best cost 6, reached twice:
  - id 909 (C3 x (D8 : Q8)), seed 2: E1=86,190,101,7,52 E2=106,72,146,0,100, breakdown 1,1,1,1,1,1.
  - id 865 (C3 x ((C4 : C8) : C2)), seed 8: E1=3,16,125,103,8 E2=172,169,53,168,21, breakdown 0,1,1,0,2,2.
- Per-group best (mean over runs): 865 6 (11.75), 909 6 (18.62), 845 8 (13.00; C6 x (C2 . ((C4 x C2):C2) = ...)),
  931 10 (11.88; C3 x (C8 : Q8)), 171 11 (12.25), 861 11 (14.00; C3 x (C8 : (C4 x C2))), 173 12, 834 12, 816 12,
  903 12, 895 12, 814 12.
- Most groups stay at 12-16 with 2 seeds, so the spread is wide and the cost-6 hits came from single seeds.

## Next (for Opus)
Cost 6 is the best in this block, on 865 and 909 only. 909 misses one element in every condition. 865 seed 8 misses
in C2, C3 (1 each) and C5, C6 (2 each). The 8 s runs did only 385-973 steps, so a group cannot be judged reliably from
this; a longer run (30 s or more) on 865 and 909 is the next check.
