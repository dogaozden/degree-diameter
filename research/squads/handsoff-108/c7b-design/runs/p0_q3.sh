#!/bin/bash
# P(point cost = 0) for random full lifts at q=3 (hexeval ITERS=0), S samples per m
cd /home/user/degree-diameter/research/squads/handsoff-108/c7b-design
S=$1; shift
out=runs/p0_q3.tsv
[ -f $out ] || echo -e "m\tsamples\tzero\tmean_point_cost" > $out
for m in "$@"; do
  z=0; tot=0; n=0
  for s in $(seq $S); do
    r=$(SEED=$((30000 + 1000*s + m)) HZERO=0 M=$m ITERS=0 nice -n 10 ./src/hexeval 3 2>&1 | grep RESULT)
    pc=$(echo "$r" | awk '{print $(NF-2)-100*$NF}')
    n=$((n+1)); tot=$((tot+pc)); [ "$pc" -eq 0 ] && z=$((z+1))
  done
  echo -e "$m\t$n\t$z\t$((tot/n))" >> $out
done
echo done >> $out.done
