#!/bin/bash
# usage: batch.sh BASE D secs seed-list n-list  (sequential runs, one thread)
B=/home/user/degree-diameter/research/frontier/beyond13
cd /home/user/degree-diameter/research/squads/beyond13/r4/g01
BASE=$1; D=$2; SECS=$3; SEEDS=$4; NS=$5; TAG=$6
for n in $NS; do for s in $SEEDS; do
  out=runs/${TAG}_D${D}_n${n}_s${s}
  r=$(THREADS=1 timeout 105 nice -n 10 $B/bin/lift $BASE $n $D $SECS $s $out ${T0:-2.0} ${T1:-0.05} ${LL:-400} 2>&1 | grep RESULT)
  echo "$r seed=$s" >> runs/log.txt
  if echo "$r" | grep -q "best=0 "; then echo "HIT $out" >> runs/log.txt; fi
done; done
