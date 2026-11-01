#!/bin/bash
# usage: chain.sh TAG KIND P N SEEDBASE NLINKS SECS [STARTFILE]
# Chains haar_big0 links (ORBIT "3 2 0", K=8); each link starts from TAG.best.orb; stops at cost 0.
B=/home/user/degree-diameter/research/frontier/beyond13
cd /home/user/degree-diameter/research/squads/beyond13/r5/h13
TAG=$1; KIND=$2; P=$3; N=$4; SB=$5; NL=$6; SECS=$7; START0=$8
for i in $(seq 1 $NL); do
  SEED=$((SB + i))
  if [ -s $TAG.best.orb ]; then export START=$PWD/$TAG.best.orb; elif [ -n "$START0" ]; then export START=$START0; else unset START; fi
  ORBIT="3 2 0" THREADS=1 timeout 200 nice -n 10 $B/bin/haar_big0 6 14 $SECS $SEED 8 $TAG.out $KIND $P $N > $TAG.$SEED.log 2>&1
  echo "link $i seed $SEED: $(grep RESULT $TAG.$SEED.log | tail -1)" >> $TAG.chain.txt
  if grep -q "best=0 " $TAG.$SEED.log; then echo "SOLVED seed $SEED" >> $TAG.chain.txt; break; fi
done
echo CHAIN_END >> $TAG.chain.txt
