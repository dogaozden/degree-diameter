#!/bin/bash
# c1 batch: SA (30 s) on the 1-involution groups, then exhaustive run on the first 20 three-involution groups.
C=/home/user/degree-diameter/research/squads/d75-r1/c1
R=/home/user/degree-diameter/research/d75-raise/src
export LOGDIR=$C/logs CANDDIR=$C/cand TMPDIR=$C/tmp MAXEV=10000000 GAPT=600 EXHT=900
mkdir -p $C/tmp/d75 $C/logs/sa
for id in 1 3 8 183 564; do
  F=$C/tmp/d75/g640_$id.ht
  timeout 300 nice -n 10 gap -q -c "N:=640;; ID:=$id;; OUT:=\"$F\";;" $R/export.g > /dev/null 2>&1
  SECS=30 SEED=1 timeout 300 nice -n 10 $R/haar75 $F sa > $C/logs/sa/640_$id.out 2>&1
  tail -1 $C/logs/sa/640_$id.out | sed "s/^/640 $id /" >> $C/logs/sa_summary.txt
  rm -f $F
done
ids=$(awk '$1==640 && $4=="false" && $3==3 {print $2}' $C/inv_all.txt | head -20)
for id in $ids; do timeout 900 $R/run1.sh 640 $id; done
echo BATCH DONE >> $C/logs/sweep.txt
