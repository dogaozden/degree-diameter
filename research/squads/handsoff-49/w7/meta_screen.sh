#!/bin/bash
# screen metacyclic groups with a non-central involution: build table, SA on each non-central involution class
cd /home/user/degree-diameter/research/squads/handsoff-49/w7
LOG=$PWD/results_meta.tsv
: > $LOG
while read m k r N; do
  name="meta_${m}_${k}_${r}"
  if [ ! -s tabs/$name.bin ]; then
    nice -n 10 python3 ../tools/groups.py "meta $m $k $r" tabs/$name.bin > /dev/null 2>&1 || { echo "build failed $name" >> $LOG; continue; }
  fi
  nice -n 10 python3 batch.py $LOG 6 50000 tabs/$name.bin >> batch_meta_stdout.log 2>&1
  rm -f tabs/$name.bin
done < meta_screen_list.txt
echo ALLDONE >> $LOG
