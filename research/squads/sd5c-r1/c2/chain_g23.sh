#!/bin/bash
cd /home/user/degree-diameter/research/squads/sd5c-r1/c2
until grep -qE "^(DONE|BUDGET)" run_g1_7_120_3_5.txt 2>/dev/null; do sleep 3; done
timeout 900 nice -n 10 env K=13 TYPES=1,3 SECS=20 STOPFIRST=1 MAXSOL=1 TBUDGET=150 ./fsd_x mat 11 50 2 0 0 10 > run_g2_11_50_2_10.txt 2>&1
timeout 900 nice -n 10 env K=13 TYPES=1,3 SECS=20 STOPFIRST=1 MAXSOL=1 TBUDGET=150 SHUFFLE=1 ./fsd_x mat 5 240 2 0 0 3 > run_g3_5_240_2_3.txt 2>&1
echo CHAIN_DONE > chain_done.txt
