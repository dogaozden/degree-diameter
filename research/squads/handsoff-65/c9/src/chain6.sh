#!/bin/sh
# after chain5: tabu 240 s from the best 3+3 vl solution (C29:C4, n = 696)
cd /home/user/degree-diameter/research/squads/handsoff-65/c9
while kill -0 19258 2>/dev/null; do sleep 10; done
INIT=sol SECS=240 SEED=6 timeout 600 nice -n 10 ../shared/tabu runs/E_L14_116_1.base groups/sg_116_1.txt runs/tabu_116_1_s6.sol > runs/tabu_116_1_s6.out 2> runs/tabu_116_1_s6.err
