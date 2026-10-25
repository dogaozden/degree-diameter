#!/bin/bash
# card c1 sweep: classes 1,5,0 in that order; every (base, group) at 60 s, PAR=1
cd /home/user/degree-diameter/research/theorems/chartlift
C=/home/user/degree-diameter/research/squads/r3-chartlift/c1
for c in 1 5 0; do
  BIN=$C/ctrl_search PAR=1 SEED=1 timeout 7000 nice -n 10 r3/batch.sh $C/jobs_sweep.txt /home/user/degree-diameter/research/theorems/chartlift/r3/k4q3_diag_cls$c.flags 60 $C/runs/sweep_cls$c > $C/runs/sweep_cls$c.log 2>&1
done
echo SWEEP_DONE
