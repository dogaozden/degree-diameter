#!/bin/bash
# farm: haar_fast d=9 D=5, 20 s per seed, single-threaded. usage: farm.sh TAG "m k r n" SEED1 SEED2
cd /home/user/degree-diameter/research/squads/hunt-d5/r4/c4
TAG=$1; SPEC=$2
for s in $(seq $3 $4); do
  THREADS=1 SAVEBEST=1 COOL=6 REHEAT=30 timeout 40 nice -n 10 ../../tools/haar_fast 9 5 20 $s 8 ${TAG}_$s.txt meta $SPEC > ${TAG}_$s.log 2>&1
  echo "$TAG seed $s $(grep -o 'best=[0-9]*' ${TAG}_$s.log | tail -1)"
done
