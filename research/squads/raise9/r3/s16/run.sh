#!/bin/bash
# usage: run.sh "<orbit k m f>" <seed> <samples> <timeout> sl|psl p n
B=/home/user/degree-diameter/research/squads/raise9/bin
ORB="$1"; SEED=$2; M=$3; TO=$4; shift 4
LOG=/home/user/degree-diameter/research/squads/raise9/r3/s16/raw.log
echo "=== $(date +%T) ORBIT=$ORB seed=$SEED samples=$M group=$*" >> $LOG
ORBIT="$ORB" RANDORB=$M THREADS=1 timeout $TO nice -n 10 $B/haar_big0 16 9 60 $SEED 1 /dev/null "$@" >> $LOG 2>&1
echo "rc=$?" >> $LOG
tail -n 3 $LOG
