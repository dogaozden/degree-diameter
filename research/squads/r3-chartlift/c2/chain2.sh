#!/bin/bash
F=/home/user/degree-diameter/research/squads/r3-chartlift/c2
cd /home/user/degree-diameter/research/theorems/chartlift
while [ "$(grep -c '^g2' $F/runs/batchB1.log 2>/dev/null)" -lt 4 ]; do sleep 3; done
BIN=$F/ctrl_search PAR=1 nice -n 10 r3/batch.sh $F/jobs_c1.txt r3/k4q3_diag_cls1.flags 60 $F/runs > $F/runs/batchC1.log 2>&1
echo CHAIN2_DONE > $F/runs/chain2.done
