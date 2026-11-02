# round2 c5 notes (Haiku worker c5)
Start 23:55:45. Time box 60 min (end 00:55).
Scanner: round2/c5/scan.sh reads todo.txt ("ORD ID SEED TABPATH"), runs shared/tabu15 TAB SEED 8 EDGES, appends to raw.txt.
Part A: all 63 non-abelian groups of orders 195, 196, 198, 200 (groups/ tables), seeds 1..3 x 8 s, seed-major order.
Part A done: todoA.txt (189 lines = 63 non-abelian groups of 195/196/198/200 x seeds 1..3), results in raw.txt (rows with order 195-200).
Part B: 60 order-192 ids spread over the complement of round2/c3/ids.txt and round2/c4/ids.txt (cand60.txt, exported by
  shared/gapw -c 'ORDER:=192; IDS:=[...]; OUTDIR:="round2/c5/tabs";' tools/gap_fast.g in 3 calls of 20). 192_175 = C96 x C2 is abelian, skipped.
  todo.txt: 59 non-abelian groups x seeds 1..2 x 8 s (seed-major), same scan.sh.

## Results (finished 00:41)
Runs: 307 tabu15 runs (scan.sh), raw.txt columns "ORD ID SEED BEST T_BEST" (SECS=8). No cost-0 run, so no edge files and no apsp check.
Part A (195, 196, 198, 200; 63 non-abelian groups, seeds 1..3):
- best per order: 195: 16 (195_1 = C5 x (C13:C3)); 196: 21 (196_5); 198: 21 (198_6); 200: 13 (200_19 = (C5 x C5):C8), 16 (200_3 = C25:C8).
- full table in raw.txt (rows with order 195-200).
Part B (order 192, 59 non-abelian groups from the 60 sampled ids, seeds 1..2; sample excludes round2/c3 and c4 ids; 192_175 = C96 x C2 abelian, skipped):
- best per group: 192_544 cost 10 (C3:((C2^3).(C2^3)), both seeds); 192_22 15; 192_351 15; 192_978 15; 192_43 16; 192_1 18; 192_1021 18.
- Reproduced 192_544 seed 1: RES best=10 (E1=40,52,72,185,101 E2=92,166,107,43,98); shared/split15 TAB cost gives 0 0 0 0 5 5 (sum 10).
Speed at m=192: about 124 steps/s (992 iterations in 8 s).
Conclusion: no hit above 704 from these groups. The 8 s runs are too short to separate groups; seed-to-seed spread is large.
