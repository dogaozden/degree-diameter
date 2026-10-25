#!/bin/bash
# usage: run_chain.sh <k> <start.in> <seed>
cd /home/user/degree-diameter/research/squads/r4-d11D5/c3
k=$1; st=$2; s=$3
echo "SA start $k $(date)"
SECS=400 SEED=$s T0=20 T1=0.4 PF=0.3 PH=0.7 OUT=sa_$k.in OUT0=fail0_sa_$k.in timeout 1500 nice -n 10 ./po7 $st > log_sa_$k.txt 2>&1
echo "SA done $k $(date)"; tail -3 log_sa_$k.txt
echo "WPO start $k $(date)"
SECS=600 SEED=$s OUT=w_$k.in OUT0=fail0_w_$k.in timeout 1500 nice -n 10 ./wpo sa_$k.in > log_w_$k.txt 2>&1
echo "WPO done $k $(date)"; tail -3 log_w_$k.txt
