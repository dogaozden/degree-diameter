#!/bin/bash
# usage: run.sh NAME MODE SEED K START [TMAX]   MODE = t (TFULL targeted) | p (plain haar_gen3s) ; spec meta 100981 55 1490, n 1
B=/home/user/degree-diameter/research/squads/beyond11b/bin
W=/home/user/degree-diameter/research/squads/beyond11b/r6/l04
cd $W
NAME=$1; MODE=$2; SEED=$3; K=$4; ST=$5; TM=$6
export START=$ST SAVEBEST=$W/$NAME.best.txt THREADS=1
if [ "$MODE" = t ]; then
  BIN=$B/haar_gen3t; export TFULL=1 TARGP=100
else
  BIN=$B/haar_gen3s
fi
if [ -n "$TM" ]; then export TMAX=$TM COOL=15; fi
timeout 105 nice -n 10 $BIN 7 11 90 $SEED $K $W/$NAME.out.txt meta 100981 55 1490 1 > $W/$NAME.log 2>&1
RC=$?
RES=$(grep '^RESULT' $W/$NAME.log | tr -d '\n')
BEST=$(echo "$RES" | sed -n 's/.*best=\([0-9-]*\).*/\1/p')
echo "$NAME mode=$MODE seed=$SEED K=$K start=$(basename $ST) TMAX=${TM:-default} rc=$RC best=$BEST :: $RES" >> $W/runs.txt
tail -n 1 $W/runs.txt
ls -la $W/$NAME.out.txt 2>/dev/null
