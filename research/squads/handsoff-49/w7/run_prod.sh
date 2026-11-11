#!/bin/bash
# order-5040 product groups (n = 5040 for H of order 2, n = 3360 for order 3 is skipped)
cd /home/user/degree-diameter/research/squads/handsoff-49/w7
LOG=$PWD/results_prod.tsv
: > $LOG
for spec in "$@"; do
  name=$(echo "$spec" | sed -e 's/ /_/g' -e 's/\*/x/g')
  echo "building $spec" >> $LOG
  nice -n 10 python3 build_perm_prod.py "$spec" >> build_prod.log 2>&1 || { echo "build failed $spec" >> $LOG; continue; }
  nice -n 10 python3 batch.py $LOG 20 300000 "tabs/$name.bin" >> batch_prod_stdout.log 2>&1
  rm -f "tabs/$name.bin"
done
echo ALLDONE >> $LOG
