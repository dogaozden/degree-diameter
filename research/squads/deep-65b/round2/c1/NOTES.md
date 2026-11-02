# round2 c1: order 180 (n = 720), all 33 non-abelian groups (abelian skipped: 180_4, 180_12, 180_18, 180_37)

Start: 23:55:37 UTC (START.txt). 60-minute time box.

Tool: research/squads/deep-65b/shared/tabu15 TAB SEED SECS EDGES_OUT (round-1 c1 program, unchanged).
Driver: run_group.sh ORDER ID SEED_FROM SEED_TO SECS (appends the full RES line to raw.txt; writes zeros/ only on cost 0).
Command per group: `timeout 105 nice -n 15 ./run_group.sh 180 ID 1 6 12` (6 x 12 s = 72 s, under 110 s).
Phase 2 (5 best groups): seeds 7..16 x 12 s, split into two calls of 5 seeds (60 s each) per group.
Table: best cost per group = min over seeds (see table.tsv, written at the end).
