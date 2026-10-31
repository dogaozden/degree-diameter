#!/bin/bash
# 2+2 multigraph bases (k > 1024 needs hgi2, MAXK 2048), started after run_ils2 finishes
cd /home/user/degree-diameter/research/squads/handsoff-49/w4
while ! grep -q DONE_ILS2 run_ils2.log; do sleep 5; done
for k in 1243 1250; do
  for b in b22t1 b22t2; do
    ILS=1 nice -n 10 ./hgi2 $b.txt cyc:$k 90 31 1 1 ils_${b}_$k > ils3_${b}_$k.log 2>&1
    echo "$b k=$k $(grep RESULT ils3_${b}_$k.log)" >> run_ils3.log
  done
done
echo DONE_ILS3 >> run_ils3.log
