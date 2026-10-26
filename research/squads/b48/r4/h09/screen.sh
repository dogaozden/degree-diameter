#!/bin/bash
# usage: screen.sh SECONDS SEED  < lines of "BASE GROUP TAG"
T=/home/user/degree-diameter/research/squads/b48/tools
B=/home/user/degree-diameter/research/squads/b48/r4/h09
S=${1:-8}; SEED=${2:-1}
while read -r BASE GROUP TAG; do
  [ -z "$BASE" ] && continue
  line=$(THREADS=1 QUIET=1 timeout 120 nice -n 10 $T/flift $B/bases/$BASE "$GROUP" 3 9 $S $SEED 8 $B/out/$TAG 2>&1 | grep RESULT)
  echo "$BASE $GROUP $TAG :: $line" | tee -a $B/results.txt
done
