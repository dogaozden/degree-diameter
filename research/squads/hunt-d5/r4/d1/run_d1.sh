#!/bin/bash
# card d1, round 4: screen non-abelian groups of orders 343-352 as Haar graphs for (Delta,D)=(6,5).
cd /home/user/degree-diameter/research/squads/hunt-d5/r4/d1
export THREADS=1 OMP_NUM_THREADS=1 SAVEBEST=1
SECS=${SECS:-5}
SEED=${SEED:-1}
while read -u 3 N I; do
  tab=t/g${N}_${I}.bin
  if [ ! -s "$tab" ]; then
    timeout 300 nice -n 10 python3 ../../tools/gapgroup.py table $N $I $tab < /dev/null || { echo "TABFAIL $N $I"; continue; }
  fi
  timeout 120 nice -n 10 ../../tools/haar_tab 6 5 $SECS $SEED 16 o/g${N}_${I}_s${SEED} tab $tab 1 > logs/g${N}_${I}_s${SEED}.log 2>&1 < /dev/null
  echo "$N $I seed=$SEED $(grep RESULT logs/g${N}_${I}_s${SEED}.log)"
done 3< ${LIST:-groups.txt}
echo DONE
