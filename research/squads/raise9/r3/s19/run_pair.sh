#!/bin/bash
# usage: run_pair.sh KIND P N ORBIT SEED  -> one random-S sample set (RANDORB=1), appends summary to TABLE.md
KIND=$1; P=$2; NN=$3; ORB=$4; SEED=$5
B=/home/user/degree-diameter/research/squads/raise9/bin
OUT=/home/user/degree-diameter/research/squads/raise9/r3/s19/log_${KIND}${P}x${NN}_${ORB// /-}_s${SEED}.txt
ORBIT="$ORB" RANDORB=1 THREADS=1 timeout 100 nice -n 10 $B/haar_big0 19 9 60 $SEED 1 /dev/null $KIND $P $NN > $OUT 2>&1
LINE=$(grep '^RANDORB d=' $OUT)
HDR=$(grep -m1 '^group' $OUT | sed 's/, rows.*//')
echo "$KIND $P x Z$NN | ORBIT \"$ORB\" | seed $SEED | $HDR | ${LINE:-NO RESULT (see $OUT)}" >> /home/user/degree-diameter/research/squads/raise9/r3/s19/TABLE.md
echo "$LINE"; tail -2 $OUT
