#!/bin/bash
# usage: farm.sh FIRST LAST ; seeds FIRST..LAST, 20 s each, single thread
cd /home/user/degree-diameter/research/squads/hunt-d5/r3/b2
for s in $(seq "$1" "$2"); do
  line=$(THREADS=1 OMP_NUM_THREADS=1 COOL=40 timeout 45 nice -n 10 ../../tools/haar_fast 7 5 20 "$s" 32 "sol_$s.txt" meta 41 15 10 1 2>&1 | grep RESULT | tail -1)
  echo "seed=$s $line" >> log.txt
done
