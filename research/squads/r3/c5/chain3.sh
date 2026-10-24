#!/bin/bash
B=/tmp/claude-0/-home-user-degree-diameter/2744c2da-0db8-5a6f-87c3-01a128c9c95e/scratchpad/bin
D=/home/user/degree-diameter/research/squads/r3/c5
cd $D
ORBIT="3 2 2" timeout 900 nice -n 10 $B/haar_sym 8 8 240 1 8 $D/s5_sl11x91_322.txt sl 11 91 > s5_sl11x91_322.log 2>&1
ORBIT="2 4 0" timeout 900 nice -n 10 $B/haar_sym 8 8 240 1 8 $D/s6_slpsl_240.txt prod sl 7 psl 9 1 > s6_slpsl_240.log 2>&1
echo CHAIN3_DONE > chain3.done
