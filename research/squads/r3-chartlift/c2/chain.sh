#!/bin/bash
F=/home/user/degree-diameter/research/squads/r3-chartlift/c2
cd /home/user/degree-diameter/research/theorems/chartlift
L=$F/runs/batch24a.log
while [ "$(grep -c '^g24_' $L 2>/dev/null)" -lt 9 ]; do sleep 3; done
BIN=$F/ctrl_search PAR=1 nice -n 10 r3/batch.sh $F/jobs_b1.txt r3/k4q3_diag_cls1.flags 60 $F/runs > $F/runs/batchB1.log 2>&1
BIN=$F/ctrl_search PAR=1 nice -n 10 r3/batch.sh $F/jobs_b2.txt r3/k4q3_diag_cls5.flags 60 $F/runs > $F/runs/batchB2.log 2>&1
BIN=$F/ctrl_search PAR=1 nice -n 10 r3/batch.sh $F/jobs_b3.txt r3/k4q3_diag_cls0.flags 60 $F/runs > $F/runs/batchB3.log 2>&1
echo CHAIN_DONE > $F/runs/chain.done
