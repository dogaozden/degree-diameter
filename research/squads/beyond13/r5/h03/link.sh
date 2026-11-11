#!/bin/bash
# usage: GROUP="m k r" link.sh OUTNAME SEED K T0 T1 REHEAT SECS [START]
B=/home/user/degree-diameter/research/frontier/beyond13
cd /home/user/degree-diameter/research/squads/beyond13/r5/h03
OUT=$1; SEED=$2; K=$3; T0=$4; T1=$5; RH=$6; SECS=$7; ST=$8
export THREADS=1
if [ -n "$ST" ]; then export START=$ST; fi
timeout 105 nice -n 10 $B/meta/hmeta 4 13 $SECS $SEED $K $OUT $GROUP 2>&1 | grep -E "RESULT|start cost|rror" | tail -3
