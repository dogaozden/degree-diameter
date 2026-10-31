# c22 notes (card: hub types with k = 3, "1,3|1,3" and "1,3,3|1,3,3")

## Model
"1,3|1,3": A0 = G (regular), A1 = G/H (|H| = 3), B0 = G, B1 = G/K (|K| = 3). n = 2|G| + 2|G|/3 = 8|G|/3.
Block counts N = n00,n01,n10,n11 (row-major (A0B0, A0B1, A1B0, A1B1)), degree rule:
 A0: n00+n01 = 6; A1: 3(n10+n11) = 6; B0: n00+n10 = 6; B1: 3(n01+n11) = 6.
 Solutions: 4,2,2,0 (connected) and 5,1,1,1 (connected); 6,0,0,2 is disconnected (not used).
 |G| in 258..285 divisible by 3 gives n = 688..760.

## Tools (copied from c18, unchanged except paths)
- t18.c (build: gcc -O3 -march=native -o t18 t18.c -lm). Generic in k: `TLIM=secs ./t18 groups/sg_X.txt 3 4,2,2,0 SEED ITERS 12 OUT`.
  OUT.par has the block values. The printed RESULT best is the cost (pairs over 4 representatives, mcos scale).
- screen22.sh K NSPLIT SECS SEED DEADLINE TABLE... -> scan/k3_<split>.tsv (columns: group, name, K, N, best, sec).
- groups/: GAP tables for orders 258..285 (SmallGroup via shared/gap_tables.g).
- mcos (copy of shared/mcos) and check.sh (scorer).
- Calibration: mcos TYPE "1|1" on SmallGroup(342,12), SEED 4, 22 s -> cost 0, check.sh VALID n=684.

## Results
- Screen t18 10 s, 4,2,2,0, seed 1: best 14 on SmallGroup(258,2) = C2 x (C43:C3) (c18 mcos got 11 in 20 s),
  then 264_12 28, 264_31 29, 270_10 34.
  NOTE: the tsv column "best" is column 5 (column 3 is K = 3).

## Status 20:12 UTC
- Best so far: cost 6, n = 688, SmallGroup(258,2), split 5,1,1,1, seed 7, 250 s: deep/t258_2_5111_s7.edges
  (check.sh bad = 602; .par has H 37, K 66). Recorded on scoreboard.tsv.
  Restart from that state (INIT=deep/init258_6.par, seed 9, 250 s): no improvement (stays 6).
- 258_2 split 4,2,2,0, seed 3, 240 s: cost 7 (deep/t258_2_4220_s3.edges, not verified: cost 7 > 6).
- 273_3 split 5,1,1,1, seed 7, 240 s: cost 18 (worse). Screen 10 s: 273_1/273_4 best 24 (4,2,2,0), 273_3 22 (5,1,1,1).
- Screen (t18, 10 s, seed 1) all 86 nonabelian groups of orders 258..285 with 3 | |G| (split 4,2,2,0): 258_2 14,
  273_1 24, 273_4 24, 273_2 26, 264_12 28, 264_31 29, 270_10 34; split 5,1,1,1 on top 12: 258_2 11, 273_3 22,
  273_4 22, 273_2 30, 285_1 32. Results in scan/k3_4-2-2-0.tsv and scan/k3_5-1-1-1.tsv.
- Tabu rate is about 3 steps/s on n = 688 (every step scans all single moves). Plateaus after ~700 steps.
