#!/bin/bash
# usage: chain.sh TAG sl|psl p n SEED0 DEADLINE_EPOCH
B=/home/user/degree-diameter/research/frontier/beyond13
D=/home/user/degree-diameter/research/squads/beyond13/r5/h14
TAG=$1; FAM=$2; P=$3; NN=$4; SEED=$5; DL=$6
OUT=$D/$TAG.out
cd $D
link=0
while [ "$(date +%s)" -lt "$DL" ] && [ ! -f $D/STOP ]; do
  link=$((link+1)); SEED=$((SEED+1))
  if [ -f $OUT.best ]; then ST="START=$OUT.best"; else ST="X=1"; fi
  env $ST ORBIT="3 2 1" THREADS=1 timeout 200 nice -n 10 $B/bin/haar_big0 7 14 95 $SEED 8 $OUT $FAM $P $NN >> $D/$TAG.log 2>&1
  if grep -q "best=0 " $D/$TAG.log 2>/dev/null && [ -f $OUT ] && tail -3 $D/$TAG.log | grep -q "best=0"; then echo "SOLVED link $link" >> $D/$TAG.log; break; fi
done
echo "CHAIN END $(date)" >> $D/$TAG.log
