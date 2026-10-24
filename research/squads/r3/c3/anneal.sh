#!/bin/bash
# usage: anneal.sh TAG SECONDS SEED ALPHA AR GROUP...   (ORBIT 3 3 1, K=8)
B=/tmp/claude-0/-home-user-degree-diameter/2744c2da-0db8-5a6f-87c3-01a128c9c95e/scratchpad/bin
TAG=$1; SEC=$2; SEED=$3; AL=$4; AR=$5; shift 5
OUT=/home/user/degree-diameter/research/squads/r3/c3/sol_${TAG}_s${SEED}.txt
LOG=/home/user/degree-diameter/research/squads/r3/c3/log_${TAG}_s${SEED}.log
if [ "$AR" = "-" ]; then
  ALPHA=$AL ORBIT="3 3 1" timeout 900 nice -n 10 $B/haar_sym 10 5 $SEC $SEED 8 $OUT "$@" > $LOG 2>&1
else
  ALPHA=$AL AR=$AR ORBIT="3 3 1" timeout 900 nice -n 10 $B/haar_sym 10 5 $SEC $SEED 8 $OUT "$@" > $LOG 2>&1
fi
echo "$TAG seed=$SEED alpha=$AL ar=$AR : $(grep -h RESULT $LOG | tail -1)" >> /home/user/degree-diameter/research/squads/r3/c3/summary.txt
