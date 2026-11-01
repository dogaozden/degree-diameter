# c3 (deep-65b round 1): hubk TABLE 5 ex on non-abelian groups of orders 290-315

Start 2026-11-01 23:09:15Z, 60-minute box. Folder only; no git; no background processes.

## Setup
- hubk.c copied from shared/hubk.c; built: `gcc -O3 -march=native -o hubk hubk.c -lm` (no warnings).
- Tables: `timeout 100 nice -n 15 /home/user/degree-diameter/research/squads/deep-65b/shared/gapw -c 'ORDER:=290; OUTDIR:="tabs"; IDS:=[1,2,3];' /home/user/degree-diameter/research/squads/deep-65b/shared/gap_tables.g`
  (same for ORDER:=300 with IDS = the 45 non-abelian ids). Plain format: m, then m x m table, identity 0.
- GAP list of non-abelian groups: 290: ids 1,2,3 (C29 x D10, C5 x D58, D290). 295: none (only C295).
  300: 45 ids (all except abelian 4, 12, 21, 49). 305: 305_1 (C61:C5). 310: ids 1-5. 315: ids 1, 3.
  Every order here is divisible by 5, so every group has a subgroup of order 5.
- Validation: `./hubk tabs/sg_290_{1,2,3}.txt 5 rand 200 1` -> 0 mismatches each. For 300 groups `rand 100 1` -> 0 mismatches each
  (out/count_300_a.txt, out/count_300_b.txt). Note: none of the random states was all-zero (validation only).
- Leaf counts: `COUNT=1 ./hubk TABLE 5 ex` (out/count_300_*.txt, out/leaf_totals_300.txt).
- Run commands: `./hubk TABLE 5 ex NPROC PROC` with NPROC 1 (290_2, 290_3) or 8/10 chunks (290_1 with 10 chunks, 300 with 8 chunks
  via run_jobs.sh). Chunks split the second-level index S[1] modulo NPROC; chunk leaf counts sum to the COUNT total (290_1: 3417508683 = 10 chunks).

## Results
- 290_1 (C29 x D10, n = 696): exact, 10 chunks, 3.42e9 leaves, 0 pass the hub-level filter (3)(6), 0 pass (2)(5),
  0 solutions. No state gets to the miss count (best miss not defined; the code records misses only after the filters).
- 290_2 (C5 x D58): exact, 3.4e8 leaves, 22.6 s (quiet machine), 0 pass (3)(6), no solution.
- 290_3 (D290): exact, 3.4e8 leaves, 16.9 s CPU, 0 pass (3)(6), no solution.
- 300 groups: see out/ex_300_<id>_p<k>of8.txt and the table in the final report. Tool runs via run_jobs.sh in smallest-leaf order.

## Command notes
- An earlier command with two runs back to back exceeded 110 s, was moved to background (task bqb0lgxm5); it was stopped
  with TaskStop at once. Its partial output (290_1 chunk 0 of 4) was discarded and the chunks were redone.
