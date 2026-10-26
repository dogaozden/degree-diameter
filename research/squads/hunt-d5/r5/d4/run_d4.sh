#!/bin/bash
# card d4, round 5: haar_tab d=6 D=5, 2 seeds x 5 s per group, groups from LIST (lines "N I").
cd /home/user/degree-diameter/research/squads/hunt-d5/r5/d4
export THREADS=1 OMP_NUM_THREADS=1 SAVEBEST=1 COOL=10 REHEAT=40
while read -u 3 N I; do
  tab=t/g${N}_${I}.bin
  src=../../r4/d1/t/g${N}_${I}.bin
  if [ ! -s "$tab" ]; then
    if [ -s "$src" ]; then cp "$src" "$tab"; else
      timeout 300 nice -n 10 python3 ../../tools/gapgroup.py table $N $I $tab < /dev/null || { echo "TABFAIL $N $I" >> farm.log; continue; }
    fi
  fi
  for seed in 1 2; do
    r=$(timeout 25 nice -n 10 ../../tools/haar_tab 6 5 5 $seed 16 o/g${N}_${I}_s${seed} tab $tab 1 2>/dev/null < /dev/null | grep RESULT)
    echo "$N $I seed=$seed $r" >> farm.log
  done
done 3< ${LIST:-groups_all.txt}
echo DONE >> farm.log
