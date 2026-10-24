#!/bin/bash
# usage: run_pv.sh k mlo mhi restarts steps tag
S=/tmp/claude-0/-home-user-degree-diameter/f8a36126-b548-5f60-bd9a-01a3e8198698/scratchpad
k=$1
for m in $(seq $2 $3); do
  ./export_all.sh $m $S/pv_all_$6.txt > /dev/null 2>&1
  awk -v pre="$S/pv_$6_" 'NF==3 && $3==0 {id=$2; f=pre id ".txt"; printf "" > f; next} {print >> f}' $S/pv_all_$6.txt
  ng=$(awk 'NF==3' $S/pv_all_$6.txt | wc -l)
  for id in $(seq 1 $ng); do
    out=$(./pvctrl2 $S/pv_$6_$id.txt $k $id $4 $5 $7)
    echo "$out" | grep CTRL | sed "s/^/m=$m id=$id /" >> pv2d_found_k$k.txt
    echo "k=$k m=$m id=$id: $(echo "$out" | tail -1)" >> pv2d_log_k$k.txt
  done
done
