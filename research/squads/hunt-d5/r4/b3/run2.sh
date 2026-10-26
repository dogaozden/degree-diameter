#!/bin/bash
# 6 more seeds on the 3 best screened groups
cd "$(dirname "$0")"
T=../../tools
: > screen2.txt
for g in "624 134" "640 19095" "648 532"; do
  set -- $g
  for s in 4002 4003 4004 4005 4006 4007; do
    r=$(THREADS=1 OMP_NUM_THREADS=1 timeout 60 nice -n 10 $T/haar_tab 7 5 8 $s 16 o2_$1_$2_$s.edges tab t$1_$2.bin 1 2>/dev/null | grep RESULT)
    echo "$1 $2 seed=$s :: $r" >> screen2.txt
  done
done
echo DONE >> screen2.txt
