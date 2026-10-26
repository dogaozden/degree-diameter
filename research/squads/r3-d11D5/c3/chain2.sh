#!/bin/bash
# second chain: cooler anneals (T0=3 T1=0.1), sequential
cd /home/user/degree-diameter/research/squads/r3-d11D5/c3
run() { name=$1; start=$2; SECS=${SECS:-360} SEED=$3 T0=3 T1=0.1 PF=0.3 PH=0.7 OUT=runs/best_$name.in OUT0=runs/fail0_$name.in timeout 900 nice -n 10 ./po7 $start > runs/log_$name.txt 2>&1; tail -n 2 runs/log_$name.txt; }
while kill -0 5949 2> /dev/null; do sleep 2; done
run aB2 starts/s_a_absolute_00_5.in 1
run fA2 runs/f5extA.in 1
run bC2 starts/s_b_absolute_00_16.in 1
echo CHAIN_DONE
