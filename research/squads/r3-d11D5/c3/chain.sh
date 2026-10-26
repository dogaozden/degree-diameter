#!/bin/bash
# sequential anneals (one heavy process at a time)
cd /home/user/degree-diameter/research/squads/r3-d11D5/c3
run() { name=$1; start=$2; SECS=${SECS:-360} SEED=$3 T0=20 T1=0.5 PF=0.3 PH=0.7 OUT=runs/best_$name.in OUT0=runs/fail0_$name.in timeout 900 nice -n 10 ./po7 $start > runs/log_$name.txt 2>&1; tail -n 2 runs/log_$name.txt; }
run bA starts/s_b_absolute_00_0.in 1
run aB starts/s_a_absolute_00_5.in 1
run bC starts/s_b_absolute_00_16.in 1
if [ -f runs/f5ext.in ]; then run fD runs/f5ext.in 1; fi
echo CHAIN_DONE
