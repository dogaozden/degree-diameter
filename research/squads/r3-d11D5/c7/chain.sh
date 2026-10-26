#!/bin/bash
cd /home/user/degree-diameter/research/squads/r3-d11D5/c7
until grep -q RESULT run1.log; do sleep 5; done
timeout 900 nice -n 10 env THREADS=1 SECS=200 SEED=13 T0=20 T1=0.5 PF=0.3 PH=0.7 OUT=run13_best.in OUT0=run13_fail0.in ./orb st13_inc8_2.in g13_inc8_2.grp > run13.log 2>&1
timeout 900 nice -n 10 env THREADS=1 SECS=200 SEED=5 T0=20 T1=0.5 PF=0.3 PH=0.7 OUT=run5_best.in OUT0=run5_fail0.in ./orb st5_inc8_2.in g5_inc8_2.grp > run5.log 2>&1
echo CHAIN_DONE > chain.done
