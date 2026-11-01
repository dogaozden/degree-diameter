#!/bin/bash
# deep2.sh: restarts from the best deep solution (cost 76) with wtt, 10 min each
W=/home/user/degree-diameter/research/squads/handsoff-49/w12
cd $W
nice -n 10 timeout 660 ./wtt bases/b4_mh2_1.txt groups/pgl11.bin 9 600 21 runs/d2_r21 10 20 100 10 10 runs/d1_mh2_1_s11.best.sol > logs/d2_r21.out 2> logs/d2_r21.err
echo "d2_r21 $(grep RESULT logs/d2_r21.out | head -1)" >> logs/deep2_summary.txt
nice -n 10 timeout 660 ./wtt bases/b4_mh2_1.txt groups/pgl11.bin 9 600 22 runs/d2_r22 10 40 200 10 30 runs/d1_mh2_1_s11.best.sol > logs/d2_r22.out 2> logs/d2_r22.err
echo "d2_r22 $(grep RESULT logs/d2_r22.out | head -1)" >> logs/deep2_summary.txt
echo DONE >> logs/deep2_summary.txt
