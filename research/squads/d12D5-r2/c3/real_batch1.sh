#!/bin/bash
# Step 2: real runs, chart held fixed (PV=1.0), groups with fake cost 0; one at a time.
C3=/home/user/degree-diameter/research/squads/d12D5-r2/c3
D=/home/user/degree-diameter/research/d12D5
BASE=$D/base_k33m.txt
mkdir -p $C3/runs
: > $C3/real_results.txt
run_real() {
  local grp=$1 tab=$2 chart=$3 seed=$4
  local out=$C3/runs/${grp}_${chart}_s${seed}
  local t0=$(date +%s)
  WRITEBEST=1 DIAGBT=1 INIT_ECHART=$D/diag/${chart}.echart timeout 600 nice -n 10 $D/mlift_ejoint2 $BASE $tab 120 $seed 2 1.0 $out > $out.log 2>&1
  local rc=$?
  local t1=$(date +%s)
  local line=$(grep -o 'best_cost=[0-9-]*' $out.log | head -1)
  local its=$(grep -o 'iters=[0-9]*' $out.log | head -1)
  printf "%s\t%s\t%s\t%s\tseed=%s\trc=%s\twall=%ss\n" "$grp" "$chart" "${line:-NA}" "${its:-NA}" "$seed" "$rc" "$((t1-t0))" >> $C3/real_results.txt
}
run_real g24_meta3_8_2 $C3/g24_meta3_8_2.txt bt3_k33m_0 2
run_real g24_dicyc6 $C3/g24_dicyc6.txt bt3_k33m_0 2
run_real g24_SL23 $C3/g24_SL23.txt bt3_k33m_0 2
run_real g24_z3xq8 $C3/g24_z3xq8.txt bt3_k33m_0 2
echo REAL1_DONE >> $C3/real_results.txt
