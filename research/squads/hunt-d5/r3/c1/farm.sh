#!/bin/bash
# usage: farm.sh FIRST LAST  (seeds, 30 s each, single thread)
cd /home/user/degree-diameter/research/squads/hunt-d5/r3/c1
for s in $(seq $1 $2); do
  out=$(THREADS=1 OMP_NUM_THREADS=1 timeout 75 nice -n 10 ../../tools/haar_fast 9 5 30 $s 16 sol_$s.bin meta 53 13 16 2 2>&1 | grep RESULT | tail -1)
  echo "seed=$s $out" | tee -a farm_log.txt
done
