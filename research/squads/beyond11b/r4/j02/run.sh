#!/bin/bash
# usage: run.sh SEED K
B=/home/user/degree-diameter/research/squads/beyond11b/bin
cd /home/user/degree-diameter/research/squads/beyond11b/r4/j02
S=$1; K=$2
THREADS=1 timeout 105 nice -n 10 $B/haar_gen3 5 11 95 $S $K s${S}_k${K}.txt meta 6763 23 4828 1 > log_s${S}_k${K}.txt 2>&1
rc=$?
best=$(grep -o 'best=[0-9]*' log_s${S}_k${K}.txt | tail -1)
echo "seed=$S K=$K rc=$rc $(grep -o 'RESULT.*' log_s${S}_k${K}.txt | grep -o 'time=.*') $best" >> runs.txt
echo "seed=$S K=$K rc=$rc $best"; tail -1 log_s${S}_k${K}.txt
