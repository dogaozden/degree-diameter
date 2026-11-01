#!/bin/bash
# usage: link.sh TAG SEED K SECS KIND P N   (chains from TAG.best.orb if it exists, else TAG.start.orb)
cd /home/user/degree-diameter/research/squads/beyond13/r4/g07
B=/home/user/degree-diameter/research/frontier/beyond13
TAG=$1; SEED=$2; K=$3; SECS=$4; KIND=$5; P=$6; N=$7
ST=""
if [ -s $TAG.best.orb ]; then ST=$TAG.best.orb; elif [ -s $TAG.start.orb ]; then ST=$TAG.start.orb; fi
if [ -n "$ST" ]; then export START=$ST; fi
ORBIT="3 2 0" THREADS=1 timeout 105 nice -n 10 $B/bin/haar_big0 6 14 $SECS $SEED $K $TAG.out $KIND $P $N > $TAG.$SEED.log 2>&1
echo EXIT $?
grep -E "RESULT|start cost|best=" $TAG.$SEED.log | tail -4
