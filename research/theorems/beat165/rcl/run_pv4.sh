#!/bin/bash
# usage: run_pv4.sh TAG "k1:m1 k2:m2 ..." runs steps T0   (annealing controller search, pvctrl4, every group of each order)
S=/tmp/claude-0/-home-user-degree-diameter/f8a36126-b548-5f60-bd9a-01a3e8198698/scratchpad
tag=$1
for km in $2; do
  k=${km%%:*}; m=${km##*:}
  ./export_all.sh $m $S/pv4_all_$tag.txt > /dev/null 2>&1
  awk -v pre="$S/pv4_${tag}_" 'NF==3 && $3==0 {id=$2; f=pre id ".txt"; printf "" > f; next} {print >> f}' $S/pv4_all_$tag.txt
  ng=$(awk 'NF==3' $S/pv4_all_$tag.txt | wc -l)
  for id in $(seq 1 $ng); do
    out=$(./pvctrl4 $S/pv4_${tag}_$id.txt $k $((m*100+id)) $3 $4 $5)
    echo "$out" | grep CTRL | sed "s/^/m=$m id=$id /" >> pv4_found.txt
    echo "k=$k m=$m id=$id: $(echo "$out" | tail -1)" >> pv4_log_$tag.txt
  done
done
