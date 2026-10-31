#!/bin/sh
# usage: hot.sh START_EDGES SEED T0 T1 SECS TAG   (guided SA restart from START; prints the result line)
cd "$(dirname "$0")"
S=$1; SEED=$2; T0=$3; T1=$4; SECS=$5; TAG=$6
OUTF=hot_$TAG.edges
INFILE=$S OUT=$OUTF SEED=$SEED T0=$T0 T1=$T1 SECS=$SECS timeout 300 nice -n 10 ./gsa > hot_$TAG.log 2>&1
B=$(grep RESULT hot_$TAG.log | awk '{print $3}')
C=$(../shared/score65 "$OUTF" | tail -1)
echo "TAG $TAG start=$S seed=$SEED T $T0->$T1 best=$B check: $C $(date -u +%H:%M)"
