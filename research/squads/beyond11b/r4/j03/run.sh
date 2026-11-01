#!/bin/bash
# usage: run.sh SEED K
B=/home/user/degree-diameter/research/squads/beyond11b/bin
cd /home/user/degree-diameter/research/squads/beyond11b/r4/j03
S=$1; K=$2
THREADS=1 timeout 105 nice -n 10 $B/haar_gen3 5 11 95 $S $K s${S}_k${K}.txt meta 5023 31 2886 1 > run_${S}_${K}.log 2>&1
RC=$?
RES=$(grep '^RESULT' run_${S}_${K}.log | sed 's/.*best=\([0-9]*\).*/\1/')
echo "seed=$S K=$K best=$RES exit=$RC $(date +%H:%M:%S)" >> runs.txt
echo "seed=$S K=$K best=$RES exit=$RC"
