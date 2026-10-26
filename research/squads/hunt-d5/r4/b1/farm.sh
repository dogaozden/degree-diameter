#!/bin/bash
# farm: haar_fast on Z41 x|10 Z15 (meta 41 15 10 1), 10 s per seed, single-threaded, SAVEBEST near misses
cd /home/user/degree-diameter/research/squads/hunt-d5/r4/b1
for s in $(seq $1 $2); do
  THREADS=1 SAVEBEST=1 COOL=6 REHEAT=30 timeout 25 nice -n 10 ../../tools/haar_fast 7 5 10 $s 8 f_$s.txt meta 41 15 10 1 > f_$s.log 2>&1
  echo "seed $s $(grep -o 'best=[0-9]*' f_$s.log | tail -1)"
done
