#!/bin/bash
# card b1, phase A: anneal two seeds (5 s each) per non-abelian group of order 606..622 (not 608, 616)
cd /home/user/degree-diameter/research/squads/hunt-d5/r1/b1
export OMP_NUM_THREADS=1 THREADS=1
while read N I rest; do
  T=t${N}_${I}.bin
  if [ ! -s "$T" ]; then
    timeout 180 nice -n 10 python3 ../../tools/gapgroup.py table $N $I $T || { echo "TABLEFAIL $N $I" >> phaseA.log; continue; }
  fi
  for SEED in 1 2; do
    R=$(timeout 60 nice -n 10 ../../tools/haar5 anneal $T 7 5 $SEED 2>&1 | grep RESULT)
    echo "$N $I seed=$SEED $R" >> phaseA.log
  done
done < groups.txt
echo DONE >> phaseA.log
