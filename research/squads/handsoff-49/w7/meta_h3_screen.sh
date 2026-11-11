#!/bin/bash
# metacyclic groups of order 7458..7700 (3 | N): screen order-3 non-central subgroups (n = 2N/3 in 4972..5134)
cd /home/user/degree-diameter/research/squads/handsoff-49/w7
LOG=$PWD/results_meta_h3.tsv
: > $LOG
while read m k r N; do
  name="metah3_${m}_${k}_${r}"
  if [ ! -s tabs/$name.bin ]; then
    nice -n 10 python3 ../tools/groups.py "meta $m $k $r" tabs/$name.bin > /dev/null 2>&1 || { echo "build failed $name" >> $LOG; continue; }
  fi
  ONLY_H=3 nice -n 10 python3 batch.py $LOG 15 100000 tabs/$name.bin >> batch_meta_h3_stdout.log 2>&1
  rm -f tabs/$name.bin
done < meta_h3_list.txt
echo ALLDONE >> $LOG
