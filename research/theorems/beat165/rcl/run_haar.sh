#!/bin/bash
S=/tmp/claude-0/-home-user-degree-diameter/f8a36126-b548-5f60-bd9a-01a3e8198698/scratchpad
for n in $(seq $1 $2); do
  ./export_all.sh $n $S/tabh_$3.txt > /dev/null 2>&1
  ./haarctrl < $S/tabh_$3.txt > haar_$n.out
  echo "order $n: groups $(grep -c ^group haar_$n.out), hits $(grep -c ^HIT haar_$n.out), best A-cover $(awk '/^group/ {split($4,x,"="); if (x[2]+0>m) m=x[2]+0} END {print m+0}' haar_$n.out)" >> haar_summary.txt
done
