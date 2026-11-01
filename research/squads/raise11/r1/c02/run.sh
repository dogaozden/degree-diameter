#!/bin/bash
# usage: run.sh SECONDS SEED Q K R
B=/home/user/degree-diameter/research/squads/raise11/bin
D=/home/user/degree-diameter/research/squads/raise11/r1/c02
S=$1; SEED=$2; Q=$3; K=$4; R=$5
cd $D
THREADS=1 timeout 105 nice -n 10 env SAVEBEST=$D/sb_${Q}_${SEED}.txt $B/haar_gen3s 6 11 $S $SEED 4 $D/out_${Q}_${SEED}.txt meta $Q $K $R 1 > $D/log_${Q}_${SEED}.txt 2>&1
echo "$Q $SEED $(grep RESULT $D/log_${Q}_${SEED}.txt | sed 's/.*best=//')  $(grep -o 'start cost=[0-9]*' $D/log_${Q}_${SEED}.txt)"
