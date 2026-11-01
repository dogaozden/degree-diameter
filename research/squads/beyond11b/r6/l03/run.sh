#!/bin/bash
# usage: run.sh TAG SEED K START|- MODE(T|P|L) [TMAX]   (d=5 D=12, 90 s, meta 8969 59 205 x Z_1)
B=/home/user/degree-diameter/research/squads/beyond11b/bin
DIR=/home/user/degree-diameter/research/squads/beyond11b/r6/l03
TAG=$1; SEED=$2; K=$3; ST=$4; MODE=$5; TM=${6:-1.5}
cd $DIR
ENVS="SAVEBEST=$DIR/s_$TAG.txt THREADS=1 TMAX=$TM"
if [ "$MODE" = "T" ]; then ENVS="$ENVS TFULL=1 TARGP=100"; BIN=$B/haar_gen3t; else BIN=$B/haar_gen3s; fi
if [ "$ST" != "-" ]; then ENVS="$ENVS START=$ST"; fi
env $ENVS timeout 105 nice -n 10 $BIN 5 12 90 $SEED $K $DIR/sol_$TAG.txt meta 8969 59 205 1 > $DIR/log_$TAG.txt 2>&1
rc=$?
RES=$(grep RESULT $DIR/log_$TAG.txt | tail -1)
echo "$(date +%H:%M:%S) tag=$TAG seed=$SEED K=$K start=$ST mode=$MODE tmax=$TM rc=$rc :: $RES" | tee -a $DIR/runs.txt
