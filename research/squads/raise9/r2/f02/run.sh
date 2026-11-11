#!/bin/bash
# usage: run.sh TAG SEED SECS meta m k r   (writes b_TAG.txt best, OUT_TAG.txt on solve, log.txt)
B=/home/user/degree-diameter/research/squads/raise9/bin
D=/home/user/degree-diameter/research/squads/raise9/r2/f02
TAG=$1; SEED=$2; SECS=$3; shift 3
cd $D
SAVEBEST=$D/b_$TAG.txt THREADS=1 timeout 105 nice -n 10 $B/haar_gen3s 6 9 $SECS $SEED 8 $D/OUT_$TAG.txt "$@" 1 > $D/log_$TAG.txt 2>&1
R=$(grep RESULT $D/log_$TAG.txt)
echo "$TAG seed=$SEED $* : $R" | tee -a $D/log.txt
