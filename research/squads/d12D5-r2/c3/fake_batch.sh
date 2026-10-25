#!/bin/bash
# Step 1: controller ceiling with free diagonals (FAKE=1 DIAGBT=1), one run at a time.
C3=/home/user/degree-diameter/research/squads/d12D5-r2/c3
D=/home/user/degree-diameter/research/d12D5
BASE=$D/base_k33m.txt
mkdir -p $C3/logs
: > $C3/ceiling.txt
run_fake() {
  local grp=$1 tab=$2
  local log=$C3/logs/fake_${grp}.log
  local t0=$(date +%s)
  FAKE=1 DIAGBT=1 timeout 300 nice -n 10 $D/mlift_ejoint2 $BASE $tab 40 1 2 1.0 > $log 2>&1
  local rc=$?
  local t1=$(date +%s)
  local line=$(grep -o 'best_cost=[0-9-]*' $log | head -1)
  local its=$(grep -o 'iters=[0-9]*' $log | head -1)
  printf "%s\t%s\t%s\trc=%s\twall=%ss\n" "$grp" "${line:-NA}" "${its:-NA}" "$rc" "$((t1-t0))" >> $C3/ceiling.txt
}
run_fake z24_ref $D/tables/z24.txt
run_fake g24_z2xz12 $C3/g24_z2xz12.txt
run_fake g24_z2z2z6 $C3/g24_z2z2z6.txt
run_fake g24_meta3_8_2 $C3/g24_meta3_8_2.txt
run_fake g24_dicyc6 $C3/g24_dicyc6.txt
run_fake g24_SL23 $C3/g24_SL23.txt
run_fake g24_z3xq8 $C3/g24_z3xq8.txt
run_fake g25_z5xz5 $C3/g25_z5xz5.txt
run_fake g26_dih13 $C3/g26_dih13.txt
run_fake g27_z3xz9 $C3/g27_z3xz9.txt
run_fake g27_meta9_3_4 $C3/g27_meta9_3_4.txt
echo FAKE_DONE >> $C3/ceiling.txt
