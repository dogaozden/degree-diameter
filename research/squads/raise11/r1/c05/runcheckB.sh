#!/bin/bash
cd /home/user/degree-diameter/research/squads/raise11/r1/c05
OMP_NUM_THREADS=1 nice -n 10 /home/user/degree-diameter/research/squads/raise11/bin/haarcheck_psl s_psl71_1505.out B > checkB.log 2>&1
echo "exit=$?" >> checkB.log
