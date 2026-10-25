#!/bin/bash
# exhaustive screen over free voltages (exact for the given chart); usage: screen.sh CHART_TAG CHART_FILE... (FAKE line always)
cd /home/user/degree-diameter/research/squads/d12D5-r2/c4
B=base_k1.txt
BT0=/home/user/degree-diameter/research/d12D5/diag/bt_base_k1_0.echart
BT1=/home/user/degree-diameter/research/d12D5/diag/bt_base_k1_1.echart
OUT=screen/summary.txt
: > $OUT
for t in tables/*.txt; do
  name=$(basename $t .txt)
  fake=$(EXH=1 FAKE=1 DIAGBT=1 timeout 120 nice -n 10 ./mlift_exh $B $t 1 1 2.0 1.0 | sed -n 's/.*min_cost=\([0-9]*\) count_at_min=\([0-9]*\).*/\1 \2/p')
  r0=$(EXH=1 DIAGBT=1 INIT_ECHART=$BT0 timeout 120 nice -n 10 ./mlift_exh $B $t 1 1 2.0 1.0 | sed -n 's/.*min_cost=\([0-9]*\) count_at_min=\([0-9]*\).*/\1 \2/p')
  r1=$(EXH=1 DIAGBT=1 INIT_ECHART=$BT1 timeout 120 nice -n 10 ./mlift_exh $B $t 1 1 2.0 1.0 | sed -n 's/.*min_cost=\([0-9]*\) count_at_min=\([0-9]*\).*/\1 \2/p')
  n=$(head -1 $t)
  echo "$name n=$n fake(min,count)=[$fake] bt0=[$r0] bt1=[$r1]" >> $OUT
done
echo DONE >> $OUT
