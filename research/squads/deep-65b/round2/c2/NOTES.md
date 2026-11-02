# c2 (round 2): orders 178, 182, 183, 184, 186, 188, 189, 190 (n = 712-760), tabu over (E1,E2)

Setup: order 183 exported with `shared/gapw -c 'ORDER:=183; IDS:=[1,2]; OUTDIR:="round2/c2/tabs";' tools/gap_fast.g`
(run from research/squads/deep-65b): 183_1 = C61 : C3 (non-abelian), 183_2 = C183 (abelian).
Non-abelian groups used (from groups/*.name, abelian=false): 178_1; 182_1-3; 183_1; 184_1,3,4,5,6,7,9,10,11;
186_1-5; 188_1,3; 189_1,3,4,5,6,7,8,10,11,12; 190_1-3. That is 34 groups.
Phase 1: seeds 1..6 x 12 s each (todo1.txt, driver scan.sh, command `timeout 105 nice -n 15 bash round2/c2/scan.sh round2/c2/todo1.txt`).
Phase 2: 10 more seeds (7..16) x 12 s on the 5 best groups by phase-1 cost (todo2.txt).
Results: raw.txt (one line per run, the tabu15 RES line); edges/ holds any cost-0 graph.

## Results (254 runs, all 12 s tabu15 runs; raw.txt holds every RES line)
No cost 0 anywhere. Best cost per group (runs):
- 183_1 C61:C3 (n=732): 7 (16 runs, hit 7 in 4 of them)
- 189_6 C3 x (C7:C9) (n=756): 7 (16 runs, hit 7 in 7 of them)
- 189_8 C7 : ((C3 x C3):C3) (n=756): 7 (16 runs, hit 7 in 2 of them)
- 186_2 C2 x (C31:C3) (n=744): 8 (16 runs); 189_4 C7 : (C9:C3) (n=756): 8 (16 runs)
- 186_3 C31 x S3: 9; 189_3: 9; 189_5, 189_7: 10; 184_9: 11; 189_1, 189_11: 12; 182_1, 184_1, 189_12: 13
- All others 14 or worse (182_2 18, 190_1 14, 190_2 20, 184_3 87, 178_1 (D178) 242, 190_3 284, ...).
Phase 2 (seeds 7..16) was run only on the 5 best by phase-1 (best cost, then mean): 183_1, 189_6, 189_4, 186_2, 189_8.
Within the 12 s budget the family floors at cost 7 for orders 732 and 756; nothing reached 0, so no graph was built,
score65/apsp were not needed, and no record was claimed. Time box used: about 55 minutes.
