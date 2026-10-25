#!/bin/bash
# Step 1 (FAKE annealer, one run at a time) and Step 2 (real annealer, bt charts fixed: PV = 1.0), k=1, in c4.
cd /home/user/degree-diameter/research/squads/d12D5-r2/c4
D=/home/user/degree-diameter/research/d12D5
B=base_k1.txt
for t in tables/z9m8.txt tables/z7d5.txt tables/meta7_10_6.txt tables/z5d7.txt; do
  name=$(basename $t .txt)
  FAKE=1 DIAGBT=1 timeout 300 nice -n 10 $D/mlift_ejoint2 $B $t 30 2 2.0 1.0 > logs/fake_$name.log 2>&1
  echo "FAKE $name: $(grep best_cost logs/fake_$name.log | sed 's/ volt=.*//')" >> logs/step1_summary.txt
done
WRITEBEST=1 DIAGBT=1 INIT_ECHART=$D/diag/bt_base_k1_1.echart timeout 600 nice -n 10 $D/mlift_ejoint2 $B tables/z9m8.txt 120 2 2.0 1.0 logs/real_z9m8_bt1 > logs/real_z9m8_bt1.log 2>&1
echo "REAL z9m8 bt1 (PV=1): $(grep best_cost logs/real_z9m8_bt1.log | sed 's/ volt=.*//')" >> logs/step1_summary.txt
echo DONE >> logs/step1_summary.txt
