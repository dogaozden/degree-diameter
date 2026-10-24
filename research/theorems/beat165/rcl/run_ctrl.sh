#!/bin/bash
S=/tmp/claude-0/-home-user-degree-diameter/f8a36126-b548-5f60-bd9a-01a3e8198698/scratchpad
for n in $(seq $1 2 $2); do
  ./export_order.sh $n $S/tab_$3.txt > /dev/null 2>&1
  ./ctrlsearch 1 < $S/tab_$3.txt > ctrl_$n.out
  h=$(grep -c "^HIT" ctrl_$n.out); b=$(grep "^group" ctrl_$n.out | awk '{split($7,x,"="); if (x[2]+0 > m) m = x[2]+0} END {print m}')
  g=$(grep -c "^group" ctrl_$n.out)
  echo "order $n: subgroup-cases $g, hits $h, best coverage $b of $((n/2))" >> ctrl_summary.txt
done
