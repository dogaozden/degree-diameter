#!/bin/bash
# usage: run.sh SEED K  -> one haar_gen3 run (95 s), logs to runs.txt
cd /home/user/degree-diameter/research/squads/beyond11b/r4/j07
B=/home/user/degree-diameter/research/squads/beyond11b/bin
THREADS=1 timeout 105 nice -n 10 $B/haar_gen3 7 11 95 $1 $2 s$1_k$2.sol meta 90281 61 60307 1 > run_s$1_k$2.log 2>&1
rc=$?
best=$(grep -o 'best=[0-9]*' run_s$1_k$2.log | tail -1)
echo "seed $1 K $2 rc $rc $best $(date +%H:%M:%S)" >> runs.txt
tail -1 run_s$1_k$2.log
