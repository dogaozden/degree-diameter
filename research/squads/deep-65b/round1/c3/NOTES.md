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

## Final results (23:59Z, box ends 00:09Z)
Full summary: ./summarise.sh output below (leaves = sum of chunk leaf counts; equals COUNT total for complete groups).

300_6 | C3 : (C25 | leaves 453493634 | pass(3)(6) 0 | pass(2)(5) 0 | solutions 0 | best miss none (no leaf passes (3)(6)) | chunk wall sum 40 s | complete
300_7 | S3 x D50 | leaves 492812762 | pass(3)(6) 0 | pass(2)(5) 0 | solutions 0 | best miss none (no leaf passes (3)(6)) | chunk wall sum 39 s | complete
300_11 | D300 abelian=false nilpotent=false | leaves 496970018 | pass(3)(6) 0 | pass(2)(5) 0 | solutions 0 | best miss none (no leaf passes (3)(6)) | chunk wall sum 39 s | complete
300_3 | C3 : (C25 | leaves 496970018 | pass(3)(6) 0 | pass(2)(5) 0 | solutions 0 | best miss none (no leaf passes (3)(6)) | chunk wall sum 38 s | complete
300_43 | (C2 x C2) | leaves 812793794 | pass(3)(6) 0 | pass(2)(5) 0 | solutions 0 | best miss none (no leaf passes (3)(6)) | chunk wall sum 132 s | complete
300_5 | C3 x (C25 | leaves 949238765 | pass(3)(6) 0 | pass(2)(5) 0 | solutions 0 | best miss none (no leaf passes (3)(6)) | chunk wall sum 191 s | complete
300_2 | C3 x (C25 | leaves 983345399 | pass(3)(6) 0 | pass(2)(5) 0 | solutions 0 | best miss none (no leaf passes (3)(6)) | chunk wall sum 186 s | complete
300_9 | C6 x D50 | leaves 983345399 | pass(3)(6) 0 | pass(2)(5) 0 | solutions 0 | best miss none (no leaf passes (3)(6)) | chunk wall sum 198 s | complete
300_23 | (C5 x C5) | leaves 1141940018 | pass(3)(6) 0 | pass(2)(5) 0 | solutions 0 | best miss none (no leaf passes (3)(6)) | chunk wall sum 234 s | complete
300_25 | (C5 x C5) | leaves 1142138774 | pass(3)(6) 0 | pass(2)(5) 0 | solutions 0 | best miss none (no leaf passes (3)(6)) | chunk wall sum 174 s | complete
300_8 | C25 x A4 | leaves 1142629395 | pass(3)(6) 0 | pass(2)(5) 0 | solutions 0 | best miss none (no leaf passes (3)(6)) | chunk wall sum 183 s | complete
300_13 | (C5 x C5) | leaves 1153526911 | pass(3)(6) 0 | pass(2)(5) 0 | solutions 0 | best miss none (no leaf passes (3)(6)) | chunk wall sum 138 s | complete
300_26 | C2 x ((C5 | leaves 1153526911 | pass(3)(6) 0 | pass(2)(5) 0 | solutions 0 | best miss none (no leaf passes (3)(6)) | chunk wall sum 151 s | complete
300_33 | C3 : ((C5 | leaves 1415761797 | pass(3)(6) 0 | pass(2)(5) 0 | solutions 0 | best miss none (no leaf passes (3)(6)) | chunk wall sum 179 s | complete
300_1 | C25 x (C3 | leaves 1482654405 | pass(3)(6) 0 | pass(2)(5) 0 | solutions 0 | best miss none (no leaf passes (3)(6)) | chunk wall sum 90 s | complete
300_10 | C50 x S3 | leaves 1482654405 | pass(3)(6) 0 | pass(2)(5) 0 | solutions 0 | best miss none (no leaf passes (3)(6)) | chunk wall sum 240 s | complete

Not run: 300 ids 14,15,16,17,18,19,20,22,24,27,28,29,30,31,32,34,35,36,37,38,39,40,41,42,44,45,46,47,48 (leaf totals 1.9e9-8.9e9 each; COUNT in out/leaf_totals_300.txt); 305_1 (C61:C5), 310_1-5, 315_1, 315_3 (not started, no validation or COUNT run). Order 295 has only C295 (abelian).

Every complete group: 0 leaves pass (3)(6), so no best miss is defined; no solutions.
