#!/bin/bash
# pass 1: flift K55 over all 30 groups of order 39..45, two seeds of 6 s each
cd /home/user/degree-diameter/research/squads/hunt-d5/r2/a3
export OMP_NUM_THREADS=1 THREADS=1
while read N I rest; do
  for SEED in 1 2; do
    out=$(timeout 40 nice -n 10 ../../tools/flift K55.txt g${N}_${I}.bin 5 5 6 $SEED 8 sol/p1_${N}_${I}_s${SEED} 2>&1 | grep RESULT)
    echo "$N $I seed=$SEED $out"
  done
done < groups.txt > pass1.log 2>&1
echo PASS1DONE >> pass1.log
