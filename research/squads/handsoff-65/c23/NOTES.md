# c23 notes (card: hub types "1,2|1,2", "1,4|1,4", "1,2,2|1,2,2"; c18's t18 tabu and mcos)

## Model facts (checked)
- mcos (shared/mcos) only uses FULL-SIZE double cosets (|D| = |H_a||H_b|). A hub orbit with |H| = k gives degree
  k * (number of blocks), so k must divide 6: k = 1,2,3,6 only. "1,4|1,4" is impossible in mcos/t18 as written; a
  C4 hub needs non-full double cosets (|H ∩ gKg^-1| = 2 gives 2 per block) and a new builder. Not done.
- "1,2|1,2": n = 3|G|. Blocks N = (n00,n01,n10,n11) with n00+n01 = 6, n10+n11 = 3, n00+n10 = 6, n01+n11 = 3.
  Splits: 3,3,3,0 / 4,2,2,1 / 5,1,1,2 (n00 = 6 disconnected). On D234: 4,2,2,1 is best (mcos 131 / t18 122 at 5 s);
  5,1,1,2: 204-212; 3,3,3,0: 265.
- Bad pairs (check.sh) vs t18 cost: D240_118 cost 15 -> bad 1080 (n 720).

## Tools
- c23/groups: GAP tables (gap_tables.g) for orders 172..190 and 230..252, even orders only (list_k2.txt, list_122.txt).
- c23/t18 (copied from c18, compiled here): TLIM=secs t18 TABLE 2 4,2,2,1 SEED ITERS TENURE OUT
- c23/screen23.sh K NSPLIT SECS SEED DEADLINE FILES...: t18 screen, appends scan/t<K>_<N>.tsv
- INIT format for t18: 4 lines of block values, then a line "H <hgen> K <kgen>" (the .par file has "H x K y cost c").
- Calibration: mcos "1|1" on SmallGroup(342,12): cost 0 in 14 s, check.sh VALID n=684.

## Results
- k=2, split 4,2,2,1 screen over all 308 non-abelian even-order groups 230..252 (4 s each, seed 1):
  best 240_118 (C3:(C5:(C8xC2))) cost 15; 240_87 16; 234_7 17; 240_133 17; 240_27 17; 240_35 17; 240_8 18.
  3,3,3,0 and 5,1,1,2 not screened (weaker on D234).
- Deep t18 on 240_118: seed 5 (260 s) cost 21; seed 7 restarted from the cost-15 state: stuck at 15 (no improvement in 240 s).

## k=2 deep and restart runs (20:05-20:35)
- 240_118 seed 5, 260 s: 21. Restart from the cost-15 state (INIT): no progress in 240 s (stuck at 15).
- Second seeds, 25 s each, top 10 k=2 groups: 240_16 16, 234_1 18, 230_1 19, 234_7 20, 240_27 22, 240_118 29.
- 240_16 deep 230 s (seed 3): 22. Restarts 12 s x 20 (240_16 and 240_118): best 19 (240_16 seed 27).
- Splits on 240_118, 25 s: 3,3,3,0 -> 31; 5,1,1,2 -> 52; 4,2,2,1 stays best.
- Conclusion: tabu floor for "1,2|1,2" is ~15 (bad 1080 at n = 720); longer runs do not help; restarts are as good.

## 1,2,2|1,2,2 (mcos, one split N=3,2,1,2,1,0,1,0,2; RANDCOMB=1)
- Screen 4 s over all 98 non-abelian even-order groups 172..190: best 174_2 (C3 x D58, n 696) cost 40 (bad 2436),
  180_19 (GL(2,4)) 53, 176_24 68, 182_2 70, 180_25 73, 180_30 78.
- Seed variance is large (174_2: 40 at seed 1, 55-63 at seeds 5-8; SA 240 s with seed 3: 45). mcos SA saturates fast.
- Other splits for 174_2 (4 s): 4,1,1,2,1,0,0,1,2 -> 52; 2,2,2,2,1,0,2,0,1 -> 58.

## Not done
- "1,4|1,4": needs non-full double cosets (builder), not written.
- No tabu for the two-hub-orbit 1,2,2 type (t18 handles one hub orbit per side); mcos SA only.

## Best files (scoreboard)
- best720_bad1080_240_118.edges: 1,2|1,2 on SmallGroup(240,118), n 720, cost 15, bad 1080 (verified by check.sh).
- best696_c40_174_2_122.edges: 1,2,2|1,2,2 on SmallGroup(174,2), n 696, cost 40, bad 2436.
- No graph with bad 0 and n > 684 found.

## Final runs (20:40-20:50)
- Restarts 12-60 s on 240_87, 234_7, 240_133, 240_118, 240_16 (seeds 40-69, about 35 runs): best 16 (240_87), 17.
- 240_118 seeds 51, 52 at 60 s: 20, 24. 240_16 seed 51 at 60 s: 20.
- mcos SA (RANDCOMB, SECS 10) 1,2|1,2 4,2,2,1: 240_118 35-70, 240_16 20-74 (worse than t18 here).
- Status: best k=2 cost 15 (n 720, bad 1080); best 1,2,2 cost 40 (n 696, bad 2436). No bad=0 graph.
- Next ideas if this were continued: write a full-neighbourhood tabu for two hub orbits per side (1,2,2 type);
  a non-full double-coset builder for "1,4|1,4" (degree 4 per full block plus 2 per semi-regular block); exhaustive
  check of all involution-subgroup pairs (H,K) for 240_118 (about 120 x 120 pairs, each with a short descent).
- 20:50-20:58: more restarts (240_118, 240_16, seeds 90-103, 200-216) and 1,2,2 SA seeds 20-41: no cost below 15 (k=2) or 40 (1,2,2).
- Final state at 20:58: no processes of mine running; scoreboard line for 720 (cost 15) and 696 (cost 40) logged.
