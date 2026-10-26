#!/bin/bash
# card d3 (round 5): haar_tab, (6,5), 2 seeds x 5 s per group, COOL=10 REHEAT=40, K=16
cd /home/user/degree-diameter/research/squads/hunt-d5/r5/d3
T=/home/user/degree-diameter/research/squads/hunt-d5/tools
export OMP_NUM_THREADS=1 THREADS=1 COOL=10 REHEAT=40 SAVEBEST=1
for gi in "370 3" "374 3" "378 5" "378 42" "378 43" "378 59" "382 1" "386 1" "390 11" "394 1" "398 1"; do
  set -- $gi; N=$1; I=$2; tab=tab_${N}_${I}.bin
  timeout 120 nice -n 10 python3 $T/gapgroup.py table $N $I $tab >/dev/null 2>>gen_err.log || { echo "$N $I TABLE_FAIL" >> run.log; continue; }
  for seed in 1 2; do
    out=sol_${N}_${I}_s${seed}.txt
    r=$(timeout 30 nice -n 10 $T/haar_tab 6 5 5 $seed 16 $out tab $tab 1 | grep RESULT | tr '\n' ' ')
    echo "N=$N I=$I seed=$seed $r" >> run.log
  done
done
echo DONE >> run.log
