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

## Status 20:40 UTC
- NEW BEST: cost 5, n = 688, SmallGroup(258,2), split 5,1,1,1, tenure 8, seed 41 (step 485): deep/t258_2_s41.edges,
  check.sh bad = 559 (verified). Recorded on scoreboard.tsv (line fixed to show bad=559).
  Reproduce: TLIM=240 ./t18 groups/sg_258_2.txt 3 5,1,1,1 41 100000000 8 OUT
- Tenure matters: tenure 8 found 5 (seed 41) and stayed at 5 from its state (seed 42, INIT); tenure 5 (seed 51) got 6;
  tenure 12 (seeds 7, 9, 21-25, 31) 6-11; tenure 20 (seed 11) 8.
- Also tried: 273_3 (cost 18), 258_1 (cost 33 at 50 s), 258_3..5 with 5,1,1,1 never valid (cost stuck at the
  invalid value, multi-edges): skip.

## Status 21:00 UTC (final for this session)
- Cost 5 reached again by seeds 61 (tenure 8, step 21), 71 (tenure 8, step 363), 81 (tenure 10, see log): a recurring
  floor for SmallGroup(258,2) split 5,1,1,1. 4,2,2,0 with tenure 8 (seed 5) gave 8. Tenure 5 gives 6.
- Best overall: cost 5 (bad 559, n 688), deep/t258_2_s41.edges. No cost-0 graph; no n > 684 claim.
- Next ideas (not done): (1) speed up t18 (incremental cost, or sample moves) so a 240 s run does 10x more steps;
  (2) groups 273_3/273_4/273_1 and 264_12 with tenure 8 and 5,1,1,1 (only tried tenure 12 or 10 s screens);
  (3) the 1,3,3|1,3,3 family (orders 207..228, n = 10|G|/3) which t18 does not cover (needs two hub orbits per side);
  (4) a cost-5 graph has far pairs from the 4 orbit representatives: targeted 2-switch moves toward those pairs.

## FINAL 21:00 UTC: NEW BEST cost 4
- SmallGroup(258,2), split 5,1,1,1, tenure 8, seed 91, 150 s (best at step 687): deep/t258_2_s91.edges (+ .par: H, K).
  check.sh bad = 516 (verified), n = 688. Recorded on scoreboard.tsv. Reproduce: TLIM=150 ./t18 groups/sg_258_2.txt 3 5,1,1,1 91 100000000 8 OUT
- Summary of the 258_2 runs (tenure 8 unless stated): seeds 41 and 61 and 71 -> 5; seed 91 -> 4; seed 42 INIT -> 5;
  4,2,2,0 (tenure 8) -> 8; tenure 5 -> 6; tenure 12 -> 6 to 11; tenure 20 -> 8.
- Cost 4 is not 0: no n > 684 record claim. Next: run more seeds at tenure 8 (150 s runs look as good as 240 s),
  and a run from the cost-4 state (INIT=deep/t258_2_s91.edges.par).
- INIT from the cost-4 state (seed 92, tenure 8, 150 s): stays at 4 (deep/t258_2_s92.log). Run ended 21:00 UTC; no c22 processes left.
