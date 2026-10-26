#!/bin/bash
# screen the 40 best non-metacyclic (7,5)-candidate groups by |G/G'| (ties: larger order first)
cd "$(dirname "$0")"
T=../../tools
: > screen1.txt
while read n i gg; do
  f=t${n}_${i}.bin
  [ -s "$f" ] || timeout 300 nice -n 10 python3 $T/gapgroup.py table $n $i $f > /dev/null 2>&1 || { echo "$n $i GG=$gg TABLE_FAIL" >> screen1.txt; continue; }
  r=$(THREADS=1 OMP_NUM_THREADS=1 timeout 60 nice -n 10 $T/haar_tab 7 5 8 4001 16 o1_${n}_${i}.edges tab $f 1 2>/dev/null | grep RESULT)
  echo "$n $i GG=$gg :: $r" >> screen1.txt
done < top40_list.txt
echo DONE >> screen1.txt
