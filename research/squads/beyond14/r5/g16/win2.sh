#!/bin/bash
# usage: win2.sh START_SOL SLOT LO HI OUT  -> one exhaustive 1-opt window on m=7351 k=35 r=3365 (N=257285)
cd /home/user/degree-diameter/research/squads/beyond14/r5/g16
timeout 105 nice -n 10 env THREADS=1 OPT1=1 OPT1SLOT=$2 OPT1LO=$3 OPT1HI=$4 START=$1 ./hmeta 4 14 1 1 1 $5 7351 35 3365 2>/dev/null | tail -1 | tee -a sweep_log_7351.txt
