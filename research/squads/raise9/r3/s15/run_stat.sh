#!/bin/bash
# usage: run_stat.sh "<sl|psl> <p> <n>" "<k m f>" SEED SAMPLES
B=/home/user/degree-diameter/research/squads/raise9/bin
GRP="$1"; ORB="$2"; SEED=$3; NS=$4
cd /home/user/degree-diameter/research/squads/raise9/r3/s15
OUT=$(ORBIT="$ORB" RANDORB=$NS THREADS=1 timeout 105 nice -n 10 $B/haar_big0 15 9 60 $SEED 1 /dev/null $GRP 2>&1)
MU=$(echo "$OUT" | grep -o 'mu=[0-9.]*' | tail -1)
N=$(echo "$OUT" | grep -o 'N=[0-9]*' | head -1)
SUM=$(echo "$OUT" | grep '^RANDORB d=' | tail -1)
echo "$GRP | ORBIT $ORB | $N $MU | seed $SEED | $SUM" | tee -a TABLE_RAW.txt
