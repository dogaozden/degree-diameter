#!/bin/bash
cd /home/user/degree-diameter/research/squads/hunt-d5/r3/d3
export OMP_NUM_THREADS=1 THREADS=1
: > screen.txt
for p in "360 118" "350 9" "360 120" "360 121" "360 141" "360 41" "360 51" "344 3" "344 7" "348 3" "348 6" "348 7" "352 32" "352 33" "352 34" "352 35" "352 6" "352 7" "360 10" "360 110" "360 112" "360 114" "360 12" "360 13" "360 133"; do
  set -- $p; N=$1; I=$2; T=g${N}_${I}.bin
  [ -f $T ] || timeout 120 nice -n 10 python3 ../../tools/gapgroup.py table $N $I $T >> gap.log 2>&1
  for SEED in 1 2; do
    timeout 60 nice -n 10 ../../tools/haar5 anneal $T 6 8 $SEED > run_${N}_${I}_s${SEED}.log 2>&1
    echo "$N $I seed=$SEED $(grep RESULT run_${N}_${I}_s${SEED}.log | head -1)" >> screen.txt
  done
done
echo ALLDONE >> screen.txt
