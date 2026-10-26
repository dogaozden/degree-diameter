#!/bin/bash
# farm: haar_fast on Z197 x| Z7 (meta 197 7 104), 12 s per seed, K=16 COOL=10 REHEAT=40, single-threaded
cd /home/user/degree-diameter/research/squads/hunt-d5/r4/c1
for s in $(seq $1 $2); do
  THREADS=1 SAVEBEST=1 COOL=10 REHEAT=40 timeout 30 nice -n 10 ../../tools/haar_fast 9 5 12 $s 16 g_$s.txt meta 197 7 104 1 > g_$s.log 2>&1
  echo "seed $s $(grep -o 'best=[0-9]*' g_$s.log | tail -1)"
done
