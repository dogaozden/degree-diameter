#!/bin/bash
# usage: save_best.sh WORKTAG  -> copies the scorer's final sets of WORKTAG into best_P0/P1/S3/S4.txt
cd /home/user/degree-diameter/research/squads/c157b-r2/c5 || exit 1
cp work_$1/P0.txt best_P0.txt && cp work_$1/P1.txt best_P1.txt && cp work_$1/S3.txt best_S3.txt && cp work_$1/S4.txt best_S4.txt
wc -l best_P0.txt best_P1.txt best_S3.txt best_S4.txt
