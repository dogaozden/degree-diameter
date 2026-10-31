#!/bin/bash
cd /home/user/degree-diameter/research/squads/handsoff-37/c8
echo "== L1 continue t2f 170 540s T 0.8->0.3"; nice -n 10 ./lns 170 11 540 3 0.8 0.5 2 out/L1 out/t2f_best.edges 0.3 2>&1 | grep -v "NEW BEST" | tail -4
echo "== L2 insertion seed2 170 540s T 1->0.3"; nice -n 10 ./lns 170 12 540 3 1 0.5 2 out/L2 out/ins170_s2.edges 0.3 2>&1 | grep -v "NEW BEST" | tail -4
echo "== L3 random 170 540s T 1->0.3"; nice -n 10 ./lns 170 13 540 3 1 0.5 2 out/L3 - 0.3 2>&1 | grep -v "NEW BEST" | tail -4
echo ALLDONE
