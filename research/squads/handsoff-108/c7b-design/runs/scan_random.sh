#!/bin/bash
# random-start costs (ITERS=0, no annealing): full random hexagon voltages (HZERO=0) and trivial hexagon (HZERO=1)
cd /home/user/degree-diameter/research/squads/handsoff-108/c7b-design
q=$1; S=$2; shift; shift
out=runs/scan_random_q${q}.tsv
[ -f $out ] || echo -e "q\tm\thz\tseed\tcost" > $out
for m in "$@"; do for hz in 0 1; do for s in $(seq $S); do
  c=$(SEED=$((7000 + 100*s + m + 1000*hz)) HZERO=$hz M=$m ITERS=0 timeout 900 nice -n 10 ./src/hexeval $q 2>&1 | grep RESULT | awk "{print \$(NF-2)}" ) 
  echo -e "$q\t$m\t$hz\t$s\t$c" >> $out
done; done; done
echo done >> $out.done
