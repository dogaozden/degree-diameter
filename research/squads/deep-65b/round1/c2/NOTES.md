# c2 notes (deep-65b round 1): word-based tabu for 2+2 lifts of [[a,6-a],[6-a,a]]

Start 23:08:37 UTC, end about 23:41 UTC (60-minute box, single thread, every command under 105 s).

## Files
- `lift2.c` (built as `lift2`, `gcc -O3 -march=native -o lift2 lift2.c -lm`): the evaluator and tabu search.
- `tabs/sg_171_*.tab`: GAP export of the five groups of order 171 (`shared/gapw -c 'ORDER:=171; OUTDIR:="tabs";' tools/gap_tabaut.g`).
  171_1 = C19:C9, 171_2 = C171, 171_3 = C19:C9 (other action), 171_4 = **C3 x (C19:C3)**, 171_5 = C57 x C3.
- `cal/`: calibration solutions at n = 684 (score65 bad = 0, diameter 5, checked for seeds 1, 2, 3, 5, 7 with score65; seeds 1, 2 also with apsp RESULT VALID).
- `screen/results.tsv`: 152 runs (every non-abelian group of orders 172-180, a = 2 and 3, mirrored family, 6 s each).
- `screen/long.txt`, `screen/general.txt`: longer runs on the best candidates.
- `jobs.txt`, `screen.sh`: the screening driver.

## Method
- Base vertices A0=0, A1=1, B0=2, B1=3. Class (i,j) has M_ij parallel edges with voltages in H (a set, so the lift is simple).
  Lift: A_i,h ~ B_j,h*g for each voltage g of class (i,j). Tree edges of classes (0,0), (0,1), (1,0) fixed to identity (normalisation).
- Word cost: W = sum over base sources u and targets v of #{x in H : no non-backtracking base walk of length <= 5 from u to v
  with holonomy x}. All NBT walks of depth <= 5 from the 4 sources form one tree (18,748 nodes). Parity makes depth <= 5 exactly
  the bound (<= 4 same side, <= 5 across).
- Check against BFS: `lift2 tabs/sg_171_4.tab 3 check 7 40` and `... check 9 30`: 70 random and local-move states, 0 mismatches.
  On the lift, bad unordered pairs (distance > 5) = m*W/2 exactly (m = |H|).
- Speed: about 100 us per full evaluation (18,748 nodes) on this machine under load. Full neighbourhood is about 1,500 moves (9 free voltages).
- Tabu: single-voltage moves, tabu tenure 10 to 20 (on (edge, old value)), aspiration on new best, random 3-move perturbation after `stall` iterations without a new best.
- Mirrored (Haar-type) family, option `SYM=1` (last argument of `tabu`): class (0,0) and (1,1) get equal voltage sets, class (0,1) and (1,0)
  get equal sets, all 12 voltages free, so 6 free voltages (x2 for the mirror). The Haar graph of C6 x (C19:C3) (the 684 record) lies in
  this family: its two classes are S0 = S cap H and S1 = S cap tH. This family is a subset of the general family, so any hit is a valid lift.

## Commands and results
1. Speed: `./lift2 tabs/sg_171_4.tab 3 speed 1 20000` -> 98-129 us per evaluation.
2. Check: `./lift2 tabs/sg_171_4.tab 3 check 7 40 ...` -> 0 mismatches (W vs BFS).
3. Calibration, general 9-voltage family, C3 x (C19:C3), a = 3, n = 684 (not solved):
   - `./lift2 tabs/sg_171_4.tab 3 tabu 1 40 cal/s171_4_a3_1 10 300 150 0`: best 14
   - `... tabu 2 40 ... 10 300 150 0`: best 2 (after 40 s, 3,344 iterations)
   - `... tabu 11 40 ... 10 300 0 0` (full neighbourhood): best 12
   - `... tabu 12 40 ... 10 300 150 0`: best 14
4. Calibration, mirrored family (SYM = 1), C3 x (C19:C3), a = 3, n = 684: **cost 0 found, validated**.
   Command: `./lift2 tabs/sg_171_4.tab 3 tabu SEED SECS cal/haar171_4_a3_SEED 10 100 0 1`.
   | seed | budget | time to cost 0 |
   |---|---|---|
   | 1 | 25 s | 0.51 s |
   | 2 | 25 s | 8.78 s |
   | 3 | 10 s | 4.65 s |
   | 4 | 10 s | 0.72 s |
   | 5 | 10 s | 0.20 s |
   | 6 | 10 s | not found (best 8) |
   | 7 | 10 s | 3.00 s |
   | 8 | 10 s | not found (best 8) |
   6 of 8 seeds reach cost 0 within 10 s. score65 on seeds 1, 2, 3, 5, 7: bad = 0, diameter 5, n = 684, 2052 edges. apsp: RESULT VALID (seeds 1, 2).
   So the search and the evaluator reproduce the 684 record family. The general 9-voltage family did not reach 0 in 40 s runs (best 2).
5. Screen, mirrored family, every non-abelian group of orders 172, 174, 176, 178, 180 (76 groups, 152 runs, `screen.sh`):
   no cost 0. Best per order (6 s, seed 1): 172: 364 (172_1, a = 3); 174: 24 (174_1, a = 3); 176: 36 (176_24 C11 x D16 and
   176_25 C11 x QD16, a = 2); 178: 868 (178_1 D178, a = 2); 180: 14 (180_21 C3 x (C15:C4), a = 3).
   Next best in the screen: 180_20 a = 2 (22), 180_23 a = 3 (22), 174_1 a = 2/3 (24/32), 180_5 a = 2 (26).
6. Longer mirrored runs (35 s, seed 2): 180_21 a = 3 -> 14; 180_20 a = 2 -> 22; 176_17 a = 3 -> 40; 180_23 a = 3 -> 22 (no improvement).
7. General 9-voltage family, 35 s, sample 150, seed 3: 180_21 a = 3 -> 10; 180_20 a = 2 -> 18; 174_1 a = 3 -> 16; 180_23 a = 3 -> 25.
   These are the best general-family values found; they are still far from 0.

## Reading
- Calibration success: yes, for the mirrored (Haar-type) subfamily only. The general family is not calibrated (best 2 on 684).
- No group of orders 172-180 reached cost 0 in the mirrored family, and the general family gives 10 at best (180_21, a = 3, n = 720).
  Cost W is on this evaluator's scale: bad pairs = m*W/2 (for 180_21: 90 * 10 = 900 bad unordered pairs).
- The screen used the mirrored family for speed and calibration, so it does not cover the 9-voltage family on all groups.
  Groups 172 and 178 are poor in both families (dihedral and cyclic-action groups).
