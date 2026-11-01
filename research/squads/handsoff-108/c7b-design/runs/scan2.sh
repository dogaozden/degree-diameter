#!/bin/bash
# random-start walk costs (ITERS=0, point-cost only = RESULT cost - 100*dup), full random family (HZERO=0)
cd /home/user/degree-diameter/research/squads/handsoff-108/c7b-design
q=$1; S=$2; shift; shift
out=runs/scan2_q${q}.tsv
[ -f $out ] || echo -e "q\tm\tseed\tpoint_cost\tdup" > $out
for m in "$@"; do for s in $(seq $S); do
  r=$(SEED=$((9100 + 100*s + m)) HZERO=0 M=$m ITERS=0 timeout 1500 nice -n 10 ./src/hexeval $q 2>&1 | grep RESULT)
  echo "$r" | awk -v q=$q -v m=$m -v s=$s '{printf "%s\t%s\t%s\t%d\t%d\n", q, m, s, $(NF-2)-100*$NF, $NF}' >> $out
done; done
echo done >> $out.done
