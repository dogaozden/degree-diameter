#!/bin/bash
# deep3.sh: chained restarts from the best solution so far (cost 64): 15 min, then 15 min from its own best
W=/home/user/degree-diameter/research/squads/handsoff-49/w12
cd $W
nice -n 10 timeout 960 ./wtt bases/b4_mh2_1.txt groups/pgl11.bin 9 900 31 runs/d3_s31 10 20 100 10 10 runs/d2_r21.best.sol > logs/d3_s31.out 2> logs/d3_s31.err
echo "d3_s31 $(grep RESULT logs/d3_s31.out | head -1)" >> logs/deep3_summary.txt
nice -n 10 timeout 960 ./wtt bases/b4_mh2_1.txt groups/pgl11.bin 9 900 32 runs/d3_s32 10 20 100 10 10 runs/d3_s31.best.sol > logs/d3_s32.out 2> logs/d3_s32.err
echo "d3_s32 $(grep RESULT logs/d3_s32.out | head -1)" >> logs/deep3_summary.txt
echo DONE >> logs/deep3_summary.txt
