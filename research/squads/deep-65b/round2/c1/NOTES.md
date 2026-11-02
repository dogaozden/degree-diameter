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

## Phase 2 (done 00:47): seeds 7..16 x 12 s on the top 5 (180_2, 180_6, 180_13, 180_14, 180_21)
180_2 (C9 x (C5 : C4)): best 4 at seed 11 (2.56 s); seeds 7-16 min 4, mean 8.0 over 16 seeds.
180_6 (C9 : (C5 : C4)): best 5 (seed 7); 180_14 (C15 x (C3 : C4)): best 5 (seed 15); 180_21 (C3 x (C15 : C4)): best 5 (seed 3, phase 1).
180_13 (C3 x C3 x (C5 : C4)): best 6 (phase 1 min; seeds 7-16 min 6).
Zeros: none (grep ' best=0 ' raw.txt is empty). No graph was built (no cost 0), so no apsp/score65 check was needed.
Full table: table.tsv (per group: best cost, number of seeds, mean cost, name). Raw RES lines: raw.txt.

## Result
- Order 180 (n = 720), 33 non-abelian groups: best cost 4 (180_2), then 5 (180_6, 180_14, 180_21), 6 (180_13, 180_33).
- No cost 0 on any group, so no valid order-180 graph with diameter 5 in this family from these 6+10 seeds.
- Tabu is noisy: the cost-4 hit came from 1 of 16 seeds on 180_2; 16 seeds x 12 s is far from exhaustive.
- Every seed ran 12 s (except the early exit at cost 0, which never happened).
