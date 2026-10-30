#!/bin/bash
# usage: mc_run.sh TYPE SECS ORDER...   (run from research/s65): mcos over every non-abelian SmallGroup of each order,
# one line per (group, class combination) in mc_campaign/<TYPE>/summary.txt; cost-0 graphs saved as HIT_*.edges.
T=$1; S=$2; shift 2; D=mc_campaign/$(echo "$T" | tr '|,' '_-'); mkdir -p $D
for N in "$@"; do
  while [ ! -e groups/mc/export_$N.log ] || pgrep -f "ORDER:=$N;" > /dev/null; do sleep 15; done
  for f in $(ls groups/mc/sg_${N}_*.txt | sort -t_ -k3 -n); do
    b=$(basename $f .txt); grep -q "abelian=true" groups/mc/$b.name && continue
    [ -s $D/$b.log ] && continue
    TYPE="$T" SECS=$S SEED=1 RANDCOMB=${RANDCOMB:-0} EDGES=$D/$b.best.edges timeout $((S*60+300)) nice -n 5 ./tools/mcos $f > $D/$b.log 2>&1
    grep -h "^COMB" $D/$b.log | sed "s/^/$b | $(head -c 60 groups/mc/$b.name | cut -d' ' -f1) | /" >> $D/summary.txt
    grep -q "^SOL" $D/$b.log && { cp $D/$b.best.edges $D/HIT_$b.edges; echo "HIT $b" >> $D/summary.txt; }
  done
done
echo DONE >> $D/summary.txt
