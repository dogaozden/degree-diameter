#!/bin/bash
# usage: screen1.sh SECS ANNSEED CHART... ; one heavy run at a time; appends a line per chart to screen1_table.txt
D=/home/user/degree-diameter/research/squads/d12D5-r2/c8
R=/home/user/degree-diameter/research/d12D5
SECS=$1; SEED=$2; shift 2
for CH in "$@"; do
  name=$(basename "$CH" .echart)
  OUT=$D/scr_${name}_s${SEED}
  t0=$(date +%s)
  WRITEBEST=1 DIAGBT=1 INIT_ECHART="$CH" timeout 300 nice -n 10 $R/mlift_ejoint2 $R/base_k33m.txt $R/tables/z24.txt $SECS $SEED 2 1.0 $OUT > $OUT.log 2>&1
  t1=$(date +%s)
  echo "$name best_cost=$(grep -o 'best_cost=[0-9]*' $OUT.log | cut -d= -f2) chart_sing=$(grep -o 'chart_singular=[0-9]*' $OUT.log | cut -d= -f2) iters=$(grep -o 'iters=[0-9]*' $OUT.log | cut -d= -f2) wall=$((t1-t0))s" >> $D/screen1_table.txt
done
echo DONE >> $D/screen1_table.txt
