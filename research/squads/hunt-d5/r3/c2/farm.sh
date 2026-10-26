#!/bin/bash
# usage: farm.sh FIRST LAST  (seeds FIRST..LAST, 25 s each, Z53 x|16 Z26)
cd /home/user/degree-diameter/research/squads/hunt-d5/r3/c2 || exit 1
for s in $(seq "$1" "$2"); do
  THREADS=1 OMP_NUM_THREADS=1 COOL=40 timeout 60 nice -n 10 ../../tools/haar_fast 9 5 25 "$s" 32 "out_$s.bin" meta 53 26 16 1 >> farm.log 2>&1
done
