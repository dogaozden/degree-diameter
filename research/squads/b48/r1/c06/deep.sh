#!/bin/bash
# Card c06 deep runs: 30 s haar_fast 4 8 on the top three screen groups, seed $1
B=/tmp/claude-0/-home-user-degree-diameter/dc6fd85c-f533-550d-af33-040d4dcb67e6/scratchpad/bin
cd /home/user/degree-diameter/research/squads/b48/r1/c06
SEED=$1
for g in "95 12 31" "73 16 10" "95 12 49"; do
  set -- $g; m=$1; k=$2; r=$3
  line=$(THREADS=1 timeout 120 nice -n 10 $B/haar_fast 4 8 30 $SEED 8 deep_${m}_${k}_${r}_s${SEED}.txt meta $m $k $r 1 2>&1 | grep RESULT | tail -1)
  echo "N=$((m*k)) $m $k $r seed=$SEED :: $line"
done
