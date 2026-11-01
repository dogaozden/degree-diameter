#!/bin/bash
# usage: run.sh NAME SEED K P KK R [STARTFILE]   (7,11) Haar search on Z_P x| Z_KK, r = R; logs to runs.txt
B=/home/user/degree-diameter/research/squads/beyond11b/bin
W=/home/user/degree-diameter/research/squads/beyond11b/r5/k12
cd $W
NAME=$1; SEED=$2; K=$3; P=$4; KK=$5; R=$6; ST=$7
if [ -n "$ST" ]; then export START=$ST; fi
env SAVEBEST=$W/$NAME.best.txt THREADS=1 timeout 105 nice -n 10 $B/haar_gen3s 7 11 95 $SEED $K $W/$NAME.out.txt meta $P $KK $R 1 > $W/$NAME.log 2>&1
RC=$?
RES=$(grep '^RESULT' $W/$NAME.log | tr -d '\n')
BEST=$(echo "$RES" | sed -n 's/.*best=\([0-9-]*\).*/\1/p')
echo "$NAME seed=$SEED K=$K p=$P k=$KK r=$R N=$((P*KK)) start=${ST:-fresh} rc=$RC best=$BEST :: $RES" >> $W/runs.txt
tail -n 1 $W/runs.txt
ls -la $W/$NAME.out.txt 2>/dev/null
