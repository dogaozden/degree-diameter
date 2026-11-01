#!/bin/bash
# usage: run.sh TAG SEED K START_OR_dash GROUP_ARGS...   (d=5 D=12, 95 s)
B=/home/user/degree-diameter/research/squads/beyond11b/bin
DIR=/home/user/degree-diameter/research/squads/beyond11b/r5/k03
TAG=$1; SEED=$2; K=$3; ST=$4; shift 4
cd $DIR
if [ "$ST" = "-" ]; then
  env SAVEBEST=$DIR/s_$TAG.txt THREADS=1 timeout 105 nice -n 10 $B/haar_gen3s 5 12 95 $SEED $K $DIR/sol_$TAG.txt "$@" 1 > $DIR/log_$TAG.txt 2>&1
else
  env START=$ST SAVEBEST=$DIR/s_$TAG.txt THREADS=1 timeout 105 nice -n 10 $B/haar_gen3s 5 12 95 $SEED $K $DIR/sol_$TAG.txt "$@" 1 > $DIR/log_$TAG.txt 2>&1
fi
rc=$?
RES=$(grep RESULT $DIR/log_$TAG.txt | tail -1)
echo "$(date +%H:%M:%S) tag=$TAG seed=$SEED K=$K start=$ST spec=$* rc=$rc :: $RES" | tee -a $DIR/runs.txt
