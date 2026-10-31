#!/bin/bash
# usage: seg.sh TAG SEED SECS START.edges   (chains from out/TAG_cur.edges + out/TAG_w.txt when present)
cd /home/user/degree-diameter/research/squads/handsoff-37/r3e
TAG=$1; SEED=$2; SECS=$3; START=$4
if [ -f out/${TAG}_cur.edges ]; then SRC=out/${TAG}_cur.edges; else SRC=$START; fi
if [ -f out/${TAG}_w.txt ]; then export WIN=out/${TAG}_w.txt; fi
FULL=${FULL:-1} PRINT=${PRINT:-20} timeout 105 nice -n 10 ./brk $SRC $SEED $SECS $TAG 2>>out/log_${TAG}.txt | tail -1
