# Card x1 (round 3)

Read ../r1/PREAMBLE.md and ../r3/PREAMBLE.md first. Your folder: research/squads/hunt-d5/r3/x1/ (create it).

(7,5) and (9,5): escape the cost-4 local minima by a different local search. Build the GAP tables (SmallGroup(615,1) and SmallGroup(1378,2)), take the cost-4 sets (615/1: S = 0 206 135 160 343 459 282 in `../r1/b1/t615_1.bin` numbering; 1378/2: S = 0 393 357 912 48 1006 387 124 1056 in `../r2/c1/tables/g1378_2.bin` numbering) and write a tabu search with exact best-improvement swaps (cost via `haar5 eval`, or your own C), plateau moves allowed, tabu tenure 10–50. Report the best cost.
