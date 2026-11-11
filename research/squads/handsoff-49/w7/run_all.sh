#!/bin/bash
# build tables and screen them, sequentially (one heavy process at a time)
cd /home/user/degree-diameter/research/squads/handsoff-49/w7
LOG=$PWD/results_perfect.tsv
: > $LOG
for spec in "$@"; do
  name=$(echo "$spec" | sed -e 's/ /_/g' -e 's/\*/x/g')
  echo "building $spec" >> $LOG
  if [ ! -s "tabs/$name.bin" ]; then
    nice -n 10 python3 build_tabs.py "$spec" >> build.log 2>&1 || { echo "build failed $spec" >> $LOG; continue; }
  fi
  nice -n 10 python3 batch.py $LOG 20 300000 "tabs/$name.bin" >> batch_stdout.log 2>&1
done
echo ALLDONE >> $LOG
