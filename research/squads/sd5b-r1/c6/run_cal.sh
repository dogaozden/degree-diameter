#!/bin/bash
# card c6 calibration on C197 : C7 (record 1, type (3,3)), 30 s CPU per config, same seed
cd /home/user/degree-diameter/research/squads/sd5b-r1/c6
export TMPDIR=$PWD/tmp
export K=9 SECS=30 NB=48 STALL=300 SEED=2 MAXSOL=100000
K=9 SECS=30 NB=48 STALL=300 SEED=2 MAXSOL=100000 PAIRS=16 timeout 900 nice -n 15 ./sdtabu6 c197.ht 1 3 3 > cal/C_pairs.out 2>&1
K=9 SECS=30 NB=48 STALL=300 SEED=2 MAXSOL=100000 ELITE=10 PERT=1 timeout 900 nice -n 15 ./sdtabu6 c197.ht 1 3 3 > cal/D_elite.out 2>&1
K=9 SECS=30 NB=48 STALL=300 SEED=2 MAXSOL=100000 PAIRS=16 ELITE=10 PERT=1 timeout 900 nice -n 15 ./sdtabu6 c197.ht 1 3 3 > cal/E_both.out 2>&1
echo CALDONE > cal/done.txt
