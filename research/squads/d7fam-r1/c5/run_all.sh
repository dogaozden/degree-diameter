#!/bin/bash
SQ=/tmp/claude-0/-home-user-degree-diameter/0ecf9576-c77c-5462-b736-5bb1ddd9e678/scratchpad/w/sq
C5=/home/user/degree-diameter/research/squads/d7fam-r1/c5
COMMON="--pool 36936 --m 16 --sample 400 --rfile $SQ/R_q8.npy --hex $SQ/hex_q8.bin --sfile $SQ/S_q8.npy --secs 300"
cd $C5
timeout 900 nice -n 15 python3 -I mirror_sa6.py 101 $C5/r1_T01 --init $SQ/state_q8_F12.npz --T 0.1 $COMMON > $C5/r1_T01.log 2>&1
timeout 900 nice -n 15 python3 -I mirror_sa6.py 102 $C5/r2_T03 --init $SQ/state_q8_F12.npz --T 0.3 $COMMON > $C5/r2_T03.log 2>&1
timeout 900 nice -n 15 python3 -I mirror_sa6.py 103 $C5/r3_scratch --T 0.15 $COMMON > $C5/r3_scratch.log 2>&1
echo ALLDONE > $C5/done.flag
