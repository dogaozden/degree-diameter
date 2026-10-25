#!/bin/bash
# Long fibre-model annealing runs (CPU-limited by fibsa itself), sequential, single thread.
# usage: run_long.sh WP T0 T1 CYCLE PADD CMAX PREM CPU
cd /home/user/degree-diameter/research/squads/d13D7_r3/c8
export OMP_NUM_THREADS=1
WP=$1; T0=$2; T1=$3; CYC=$4; PADD=$5; CMAX=$6; PREM=$7; CPU=$8
timeout 900 nice -n 10 ./fibsa long_seed397.model $CPU 31 $WP $T0 $T1 $CYC $PADD $CMAX seed397_model.txt $PREM > long_seed397.log 2>&1
timeout 900 nice -n 10 ./fibsa long_empty.model $CPU 32 $WP $T0 $T1 $CYC $PADD $CMAX - $PREM > long_empty.log 2>&1
echo "LONG RUNS FINISHED"
