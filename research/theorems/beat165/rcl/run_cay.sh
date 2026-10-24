#!/bin/bash
S=/tmp/claude-0/-home-user-degree-diameter/f8a36126-b548-5f60-bd9a-01a3e8198698/scratchpad
for n in $(seq $1 2 $2); do
  ./export_order.sh $n $S/tabc_$3.txt > /dev/null 2>&1
  ./ctrlsearch2 < $S/tabc_$3.txt > cay_$n.out
  echo "order $n (|G0| = $((n/2))): hit groups $(grep -c '^group' cay_$n.out), hit pairs $(awk '/^group/ {split($7,x,"="); s+=x[2]} END {print s+0}' cay_$n.out)" >> cay_summary.txt
done
