#!/bin/bash
cd /home/user/degree-diameter/research/squads/sd5b-r1/c5
export TMPDIR=$PWD/tmp
K=9 SECS=60 MAXSOL=100000 SEED=3 T0=5 T1=0.5 LCYC=500000 timeout 900 nice -n 15 ./sa g31.ht 1 1 4 > nm31_r1_f1m4_sa.out 2>&1
K=9 SECS=60 MAXSOL=100000 SEED=3 T0=5 T1=0.5 LCYC=500000 timeout 900 nice -n 15 ./sa g45.ht 3 3 3 > nm45_r3_f3m3_sa.out 2>&1
echo ALLDONE > nm_done.flag
