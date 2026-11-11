#!/bin/bash
# usage: run1.sh SEED K  -> one fresh 90 s run, appends to seeds.txt
B=/home/user/degree-diameter/research/squads/raise9/bin
cd /home/user/degree-diameter/research/squads/raise9/r3/g3
S=$1; K=$2
OUT=$(SAVEBEST=b_s$S.txt THREADS=1 timeout 105 nice -n 10 $B/haar_gen3s 6 9 90 $S $K OUT_s$S.txt meta 2551 25 7 1 2>&1)
RES=$(echo "$OUT" | grep '^RESULT')
BEST=$(echo "$RES" | sed -n 's/.* best=\([0-9]*\).*/\1/p')
EV=$(echo "$RES" | sed -n 's/.* evals=\([0-9]*\).*/\1/p')
[ -f OUT_s$S.txt ] && CHK=CHECK_PENDING || CHK=no_sol
echo "$S | $K | ${BEST:-NA} | ${EV:-NA} | $CHK" >> seeds.txt
echo "$RES"
