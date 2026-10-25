#!/bin/bash
cd /home/user/degree-diameter/research/squads/d10D7-r4/c6
H=/home/user/degree-diameter/research/d10D7/hex/hex_q5.bin
timeout 100 nice -n 10 ./ls6w $H points 45 1 W_s1 - > W_s1.log 2>&1
timeout 100 nice -n 10 ./ls6w $H points 45 2 W_s2 - > W_s2.log 2>&1
echo DONE > w_done.txt
