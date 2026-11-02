# round2 c1: order 180 (n = 720), all 33 non-abelian groups (abelian skipped: 180_4, 180_12, 180_18, 180_37)

Start: 23:55:37 UTC (START.txt). 60-minute time box.

Tool: research/squads/deep-65b/shared/tabu15 TAB SEED SECS EDGES_OUT (round-1 c1 program, unchanged).
Driver: run_group.sh ORDER ID SEED_FROM SEED_TO SECS (appends the full RES line to raw.txt; writes zeros/ only on cost 0).
Command per group: `timeout 105 nice -n 15 ./run_group.sh 180 ID 1 6 12` (6 x 12 s = 72 s, under 110 s).
Phase 2 (5 best groups): seeds 7..16 x 12 s, split into two calls of 5 seeds (60 s each) per group.
Table: best cost per group = min over seeds (see table.tsv, written at the end).

## Phase 1 (done 00:36): seeds 1..6 x 12 s on all 33 non-abelian groups; raw.txt has every RES line
Best cost per group (min over 6 seeds): 180_6 5, 180_14 5, 180_21 5, 180_2 6, 180_13 6, 180_33 6, 180_1 7, 180_8 7,
180_22 7, 180_28 7, 180_5 8, 180_16 8, 180_19 8, 180_20 8, 180_24 8, 180_31 8, 180_32 8, 180_9 9, 180_15 9, 180_23 10,
180_10 11, 180_26 12, 180_35 16, 180_25 29, 180_30 31, 180_27 52, 180_7 56, 180_34 59, 180_29 63, 180_3 87, 180_17 89,
180_36 239, 180_11 247. No zero.
Top 5 for phase 2: 6, 14, 21 (cost 5); 13 and 2 (cost 6; tie with 33 broken by mean over seeds: 13 mean 6.2, 2 mean 8.0,
33 mean 8.7).
