#!/bin/bash
B=/tmp/claude-0/-home-user-degree-diameter/2744c2da-0db8-5a6f-87c3-01a128c9c95e/scratchpad/bin
D=/home/user/degree-diameter/research/squads/r3/c5
cd $D
ORBIT="4 2 0" timeout 900 nice -n 10 $B/haar_sym 8 8 300 1 8 $D/s2_psl7sl9_420.txt prod psl 7 sl 9 1 > s2_psl7sl9_420.log 2>&1
ORBIT="3 2 2" timeout 900 nice -n 10 $B/haar_sym 8 8 300 1 8 $D/s3_slpsl_322.txt prod sl 7 psl 9 1 > s3_slpsl_322.log 2>&1
./alpha_sweep.sh
echo CHAIN1_DONE > chain1.done
