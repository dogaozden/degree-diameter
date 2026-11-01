#!/bin/bash
# usage: run.sh NAME P K R SEED KK SECS [START]
B=/home/user/degree-diameter/research/squads/beyond11b/bin
D=/home/user/degree-diameter/research/squads/beyond11b/r5/k07
NAME=$1; P=$2; K=$3; R=$4; SEED=$5; KK=$6; SECS=$7; ST=$8
cd $D
TAG=${NAME}_s${SEED}_K${KK}
if [ -n "$ST" ]; then export START=$ST; fi
SAVEBEST=$D/$TAG.best THREADS=1 timeout 52 nice -n 10 $B/haar_gen3s 6 11 $SECS $SEED $KK $D/$TAG.sol meta $P $K $R 1 > $D/$TAG.log 2>&1
RES=$(grep '^RESULT' $D/$TAG.log | tail -1)
BEST=$(echo "$RES" | sed -n 's/.*best=\([0-9]*\).*/\1/p')
echo "$(date +%H:%M:%S) $TAG group=meta $P $K $R x1 N=$((P*K)) start=${ST:-none} best=${BEST:-NA} sol=$([ -f $D/$TAG.sol ] && echo yes || echo no)" >> $D/runs.txt
