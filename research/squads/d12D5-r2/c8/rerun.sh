#!/bin/bash
# usage: rerun.sh SECS ANNSEED CHART... ; longer runs at m=72; appends to rerun_table.txt; one heavy run at a time
D=/home/user/degree-diameter/research/squads/d12D5-r2/c8
R=/home/user/degree-diameter/research/d12D5
SECS=$1; SEED=$2; shift 2
for CH in "$@"; do
  name=$(basename "$CH" .echart)
  OUT=$D/rr_${name}_s${SEED}
  t0=$(date +%s)
  WRITEBEST=1 DIAGBT=1 INIT_ECHART="$CH" timeout 600 nice -n 10 $R/mlift_ejoint2 $R/base_k33m.txt $R/tables/z24.txt $SECS $SEED 2 1.0 $OUT > $OUT.log 2>&1
  t1=$(date +%s)
  echo "$name seed=$SEED secs=$SECS best_cost=$(grep -o 'best_cost=[0-9]*' $OUT.log | cut -d= -f2) iters=$(grep -o 'iters=[0-9]*' $OUT.log | cut -d= -f2) wall=$((t1-t0))s" >> $D/rerun_table.txt
done
echo DONE >> $D/rerun_table.txt
