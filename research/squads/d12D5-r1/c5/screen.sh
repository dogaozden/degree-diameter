#!/bin/bash
# step 1: controller-only screen (fake chart), K33m base, 11 non-abelian groups of order 24, SECS=30, SEED=1
cd /home/user/degree-diameter/research/squads/d12D5-r1/c5
export THREADS=1
B=/home/user/degree-diameter/research/d12D5/base_k33m.txt
F=/home/user/degree-diameter/research/d12D5/charts/fake_univ.txt
M=/home/user/degree-diameter/research/d12D5/mlift_chart
for g in D12 Dic6 Z3xZ8R2 Z3xD4 Z3xQ8 Z4xS3 Z2xD6 Z2xDic3 S4 A4xZ2 SL23; do
  s=$(date +%s)
  timeout 150 nice -n 10 $M $B t_$g.txt $F 30 1 > screen/$g.log 2>&1
  rc=$?
  echo "$g rc=$rc wall=$(( $(date +%s) - s ))s $(grep -o 'best_cost=[0-9]*' screen/$g.log)" >> screen/summary.txt
done
echo DONE >> screen/summary.txt
