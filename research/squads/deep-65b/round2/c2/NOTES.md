# c2 (round 2): orders 178, 182, 183, 184, 186, 188, 189, 190 (n = 712-760), tabu over (E1,E2)

Setup: order 183 exported with `shared/gapw -c 'ORDER:=183; IDS:=[1,2]; OUTDIR:="round2/c2/tabs";' tools/gap_fast.g`
(run from research/squads/deep-65b): 183_1 = C61 : C3 (non-abelian), 183_2 = C183 (abelian).
Non-abelian groups used (from groups/*.name, abelian=false): 178_1; 182_1-3; 183_1; 184_1,3,4,5,6,7,9,10,11;
186_1-5; 188_1,3; 189_1,3,4,5,6,7,8,10,11,12; 190_1-3. That is 34 groups.
Phase 1: seeds 1..6 x 12 s each (todo1.txt, driver scan.sh, command `timeout 105 nice -n 15 bash round2/c2/scan.sh round2/c2/todo1.txt`).
Phase 2: 10 more seeds (7..16) x 12 s on the 5 best groups by phase-1 cost (todo2.txt).
Results: raw.txt (one line per run, the tabu15 RES line); edges/ holds any cost-0 graph.
