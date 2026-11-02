#!/bin/bash
# usage: win.sh START_SOL SLOT LO HI OUT  -> one exhaustive 1-opt window (state m=7211 k=35 r=6364)
cd /home/user/degree-diameter/research/squads/beyond14/r5/g16
timeout 105 nice -n 10 env THREADS=1 OPT1=1 OPT1SLOT=$2 OPT1LO=$3 OPT1HI=$4 START=$1 ./hmeta 4 14 1 1 1 $5 7211 35 6364 2>/dev/null | tail -1 | tee -a sweep_log.txt
