#!/bin/bash
# screen top groups: one anneal (6 s) per group, seed 1
cd /home/user/degree-diameter/research/squads/hunt-d5/r1/a2
while read N I AB G Z Q; do
  T=tab/g${N}_${I}.bin
  [ -f $T ] || timeout 300 nice -n 10 python3 ../../tools/gapgroup.py table $N $I $T >/dev/null 2>&1
  R=$(OMP_NUM_THREADS=1 timeout 60 nice -n 10 ../../tools/haar5 anneal $T 5 6 1 2>&1 | grep RESULT)
  echo "$N $I q=$Q Z=$Z :: $R" >> screen_out.txt
done < screen_list.txt
echo DONE >> screen_out.txt
