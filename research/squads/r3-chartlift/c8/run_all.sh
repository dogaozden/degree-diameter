#!/bin/bash
# c8 batch: 10 product groups for (12,5) [chart k4q3_diag_cls1, base bases4/k4r1_000] then 10 for (15,5)
# [chart k5q3_pd_star23, base bases5/k5r1_000]; PAR=1, 60 s per job, seed 1.  Run from research/theorems/chartlift.
C8=/home/user/degree-diameter/research/squads/r3-chartlift/c8
cd /home/user/degree-diameter/research/theorems/chartlift || exit 1
export BIN=$C8/ctrl_search PAR=1 SEED=1
r3/batch.sh $C8/jobs12.txt r3/k4q3_diag_cls1.flags 60 $C8/runs12
r3/batch.sh $C8/jobs15.txt r3/k5q3_pd_star23.flags 60 $C8/runs15
echo ALL_DONE
