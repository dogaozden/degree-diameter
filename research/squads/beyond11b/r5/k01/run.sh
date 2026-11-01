#!/bin/bash
# usage: run.sh TAG SEED K GROUP_SPEC [START_FILE]   (GROUP_SPEC e.g. "meta 677 52 12 1")
B=/home/user/degree-diameter/research/squads/beyond11b/bin
D=/home/user/degree-diameter/research/squads/beyond11b/r5/k01
TAG=$1; SEED=$2; K=$3; SPEC=$4; START=$5
cd $D
if [ -n "$START" ]; then
  START_ENV="START=$START"; STARTLBL=$START
else
  START_ENV="X=1"; STARTLBL=none
fi
env $START_ENV SAVEBEST=$D/best_$TAG.txt THREADS=1 timeout 105 nice -n 10 $B/haar_gen3s 4 12 95 $SEED $K $D/out_$TAG.txt $SPEC > $D/log_$TAG.log 2>&1
rc=$?
res=$(grep RESULT $D/log_$TAG.log | sed 's/^RESULT //')
last=$(grep '^t=' $D/log_$TAG.log | tail -1)
echo "tag=$TAG seed=$SEED K=$K spec=[$SPEC] start=$STARTLBL exit=$rc | $res | last: $last" >> $D/runs.txt
echo "tag=$TAG exit=$rc $res"
