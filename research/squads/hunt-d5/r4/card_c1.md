# Card c1 (round 4)

Read ../r1/PREAMBLE.md, ../r3/PREAMBLE.md and ../r4/PREAMBLE.md first. Your folder: research/squads/hunt-d5/r4/c1/ (create it).

(9,5) farm + LNS on Z53 ⋊₁₆ Z26: `SAVEBEST=1 COOL=6 REHEAT=30 haar_fast 9 5 12 SEED 8 OUT meta 53 26 16 1`, seeds 10001, 10002, …; for every near miss of cost ≤ 4 run `haar5 lns ../../tables/mt_53_26_16.bin 9 "<indices>" 2 150 1` (indices via nm2idx.py). Split the budget about half farming, half LNS. Report the cost histogram and the best LNS result.
