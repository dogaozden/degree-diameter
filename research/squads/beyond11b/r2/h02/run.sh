#!/bin/bash
# usage: run.sh SECS SEED m k r TAG   -> one haar_gen3 run on meta m k r x Z_1, then checker if solved
B=/home/user/degree-diameter/research/squads/beyond11b/bin
D=/home/user/degree-diameter/research/squads/beyond11b/r2/h02
S=$1; SEED=$2; m=$3; k=$4; r=$5; TAG=$6
cd $D
THREADS=1 timeout 105 nice -n 10 $B/haar_gen3 4 11 $S $SEED 4 sol_$TAG.sol meta $m $k $r 1 > log_$TAG.txt 2>&1
echo "$TAG | $(grep RESULT log_$TAG.txt | head -1) | $(grep '^start cost' log_$TAG.txt | head -1)"
