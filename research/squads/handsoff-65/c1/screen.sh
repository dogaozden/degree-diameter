#!/bin/bash
# screen all groups of orders 171..180 with each 2+2 base (a=1,2,3), tabu from random start, SECS each
# usage: screen.sh SECS ORDERS...   -> appends to screen.tsv: order id name a cost
C1=/home/user/degree-diameter/research/squads/handsoff-65/c1
S=/home/user/degree-diameter/research/squads/handsoff-65/shared
SECS=$1; shift
for o in "$@"; do
  for f in $C1/tabs/sg_${o}_*.txt; do
    id=$(basename $f .txt | awk -F_ '{print $3}')
    name=$(cut -d' ' -f1-3 $C1/tabs/sg_${o}_${id}.name 2>/dev/null | tr ' ' '_')
    for a in 1 2 3; do
      r=$(INIT=random SECS=$SECS SEED=$((id*7+a)) timeout 100 nice -n 10 $S/tabu $C1/bases/a$a.base $f 2>/dev/null | grep RESULT)
      c=$(echo "$r" | awk '{print $3}')
      printf '%s\t%s\t%s\ta%s\t%s\n' "$o" "$id" "$name" "$a" "${c:-NA}" >> $C1/screen.tsv
    done
  done
done
echo done >> $C1/screen.tsv
