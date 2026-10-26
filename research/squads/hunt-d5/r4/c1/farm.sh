#!/bin/bash
# farm: haar_fast on Z53 x| Z26 (meta 53 26 16), 12 s per seed, single-threaded
cd /home/user/degree-diameter/research/squads/hunt-d5/r4/c1
for s in $(seq $1 $2); do
  THREADS=1 SAVEBEST=1 COOL=6 REHEAT=30 timeout 30 nice -n 10 ../../tools/haar_fast 9 5 12 $s 8 f_$s.txt meta 53 26 16 1 > f_$s.log 2>&1
  echo "seed $s $(grep -o 'best=[0-9]*' f_$s.log | tail -1)"
done
