#!/bin/bash
# control: plain tabu (fsd.c unchanged mode, NB=48) on the same benchmark, seed 1, same CPU budget
cd /home/user/degree-diameter/research/squads/sd5c-r1/c5
timeout 900 nice -n 10 env K=13 TYPES=3 REC=5 SECS=120 SEED=1 MAXSOL=1 STOPFIRST=1 ./fsd_x meta 251 20 32 1 > base_s1.txt 2>&1
echo "base seed 1 rc=$?" >> base.out
echo BASE_DONE >> base.out
