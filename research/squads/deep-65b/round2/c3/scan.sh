#!/bin/bash
# usage: scan.sh "SEEDS" SECS TODO   (foreground; each group in TODO ("order id" lines) gets each seed once)
# runs shared/tabu15 on tabs/sg_<order>_<id>.tab, appends "id seed best t_best" to raw.txt, full RES lines to res.txt.
# starts no new run after 92 s of this call; every run is SECS long, so the call stays under ~100 s.
D=/home/user/degree-diameter/research/squads/deep-65b/round2/c3
cd /home/user/degree-diameter/research/squads/deep-65b || exit 1
SEEDS=$1; SECS=$2; TODO=$3
START=$(date +%s)
mkdir -p $D/edges; touch $D/raw.txt $D/res.txt
while read ord id; do
  for seed in $SEEDS; do
    if grep -q "^$id $seed " $D/raw.txt; then continue; fi
    el=$(( $(date +%s) - START ))
    if [ $el -gt 92 ]; then echo "stopped at $el s"; exit 0; fi
    line=$(timeout 60 nice -n 15 shared/tabu15 $D/tabs/sg_${ord}_${id}.tab $seed $SECS $D/edges/sg_${ord}_${id}_s${seed}.edges)
    echo "$line" >> $D/res.txt
    best=$(echo "$line" | sed -n 's/.* best=\([0-9]*\) .*/\1/p')
    tb=$(echo "$line" | sed -n 's/.* t_best=\([0-9.]*\) .*/\1/p')
    echo "$id $seed ${best:-NA} ${tb:-NA}" >> $D/raw.txt
  done
done < $TODO
echo "all done in this call after $(( $(date +%s) - START )) s"
