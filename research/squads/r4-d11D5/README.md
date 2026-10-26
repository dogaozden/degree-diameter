# Squad round r4-d11D5 (job resume3-cell-11-5): more structural-0 DM bases, and n = 587, 588

Background and file format, scorer po7, machine rules, scoreboard format: research/squads/r3-d11D5/README.md (read it).
Round r3 results: card c2's clause-weighting search `wpo` (research/squads/r3-d11D5/c2/wpo.c, usage in its header)
took the r2 cost-2 state best_y901.in to STRUCTURAL COST 0 at n = 586 in 325 CPU s
(research/squads/r3-d11D5/c2/fail0_y901.in). Card c4 got cost 0 on W(7)+1 with simulated annealing (po7) from a
7-flag incident switch with the random-like sigma of the 4,800 record. Opus is now solving the flag cocycle (nu) on
fail0_y901.in. This round: more cost-0 bases (some may have an easier nu stage) and bigger n.
Compile wpo in your folder: gcc -O3 -march=native -o wpo /home/user/degree-diameter/research/squads/r3-d11D5/c2/wpo.c -lm
Usage: `SECS=600 SEED=1 OUT=best.in OUT0=fail0.in ./wpo start.in` (stops at true cost 0 and writes OUT0).
Machine: 4 cores shared by about 8 heavy processes. ONE heavy process per card at a time, `timeout 1500 nice -n 10`.
Scoreboard: research/squads/r4-d11D5/scoreboard.jsonl (same line format as r3). Time box: about 50 minutes.
