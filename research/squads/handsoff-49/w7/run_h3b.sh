#!/bin/bash
# build perm-product groups of order 7560 (n = 5040 for H of order 3) and screen them with batch.py
cd /home/user/degree-diameter/research/squads/handsoff-49/w7
LOG=$PWD/results_h3b.tsv
: > $LOG
for spec in "$@"; do
  name=$(echo "$spec" | sed -e 's/ /_/g' -e 's/\*/x/g')
  echo "building $spec" >> $LOG
  nice -n 10 python3 build_perm_prod.py "$spec" >> build_h3b.log 2>&1 || { echo "build failed $spec" >> $LOG; continue; }
  nice -n 10 python3 batch.py $LOG 20 300000 "tabs/$name.bin" >> batch_h3b_stdout.log 2>&1
done
echo ALLDONE >> $LOG
