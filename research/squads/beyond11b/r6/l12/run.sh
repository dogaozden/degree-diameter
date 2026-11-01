#!/bin/bash
# usage: run.sh TAG SECS SEED K START_OR_dash TFULL(0|1) TMAX GROUP_ARGS...   (d=5 D=12)
B=/home/user/degree-diameter/research/squads/beyond11b/bin
DIR=/home/user/degree-diameter/research/squads/beyond11b/r6/l12
TAG=$1; SECS=$2; SEED=$3; K=$4; ST=$5; TF=$6; TM=$7; shift 7
cd $DIR
ENVS="SAVEBEST=$DIR/b_$TAG.txt THREADS=1 TFULL=$TF TARGP=100 TMAX=$TM"
[ "$TF" = "0" ] && ENVS="SAVEBEST=$DIR/b_$TAG.txt THREADS=1 TMAX=$TM"
if [ "$ST" != "-" ]; then ENVS="START=$ST $ENVS"; fi
env $ENVS timeout 105 nice -n 10 $B/haar_gen3t 5 12 $SECS $SEED $K $DIR/sol_$TAG.txt "$@" 1 > $DIR/log_$TAG.txt 2>&1
rc=$?
RES=$(grep RESULT $DIR/log_$TAG.txt | tail -1)
echo "$(date +%H:%M:%S) tag=$TAG seed=$SEED K=$K start=$ST tfull=$TF tmax=$TM spec=$* rc=$rc :: $RES" | tee -a $DIR/runs.txt
