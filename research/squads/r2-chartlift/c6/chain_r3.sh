#!/bin/bash
# waits for the 2+2 batch (pid given as $1) to exit, then runs the restricted 3+3 batch with PAR=1
F=/home/user/degree-diameter/research/squads/r2-chartlift/c6
C=/home/user/degree-diameter/research/theorems/chartlift
while kill -0 "$1" 2>/dev/null; do sleep 5; done
cd $C && BIN=$F/ctrl_search PAR=1 SEED=1 timeout 1500 nice -n 5 bash r3/batch.sh $F/jobs_r3.txt $F/c4s2.flags 6 $F/runs_r3 > $F/batch_r3.log 2>&1
echo CHAIN_DONE
