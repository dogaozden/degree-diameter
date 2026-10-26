#!/bin/bash
# continuation of the best two-pair state (aB2) at low temperature, after the f5 extension run
cd /home/user/degree-diameter/research/squads/r3-d11D5/c3
while pgrep -f "^./po7 runs/f5extA" > /dev/null; do sleep 2; done
SECS=300 SEED=2 T0=0.5 T1=0.05 PF=0.3 PH=0.7 OUT=runs/best_aB3.in OUT0=runs/fail0_aB3.in timeout 900 nice -n 10 ./po7 runs/best_aB2.in > runs/log_aB3.txt 2>&1
tail -n 2 runs/log_aB3.txt
echo CHAIN3_DONE
