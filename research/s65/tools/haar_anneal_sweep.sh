#!/bin/bash
# usage: haar_anneal_sweep.sh SECS ORDER...  (run from research/s65): mcos TYPE "1|1" (Haar graphs) on every non-abelian
# SmallGroup of each order; one line per group in haar/anneal_<first>_<last>.txt (cost 0 = Haar graph of diameter 5).
S=$1; shift; O=haar/anneal_$1_${@: -1}.txt
for N in "$@"; do
  while [ ! -e groups/mc/export_$N.log ] || pgrep -f "ORDER:=$N;" > /dev/null; do sleep 15; done
  for f in $(ls groups/mc/sg_${N}_*.txt 2>/dev/null | sort -t_ -k3 -n); do
    b=$(basename $f .txt); grep -q "abelian=true" groups/mc/$b.name && continue
    r=$(TYPE="1|1" SECS=$S SEED=1 timeout $((S*4+60)) nice -n 5 ./tools/mcos $f 2>/dev/null | grep "^COMB" | awk '{for(i=1;i<=NF;i++) if($i=="best") print $(i+1)}')
    echo "$b $r $(head -c 70 groups/mc/$b.name | sed 's/ abelian.*//')" >> $O
  done
done
echo DONE >> $O
