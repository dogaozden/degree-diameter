#!/bin/bash
cd /home/user/degree-diameter/research/squads/handsoff-37/c2
S=../shared/seeds
for seed in $(seq 100 159); do
  k=$(( (seed % 3) * 2 + 2 ))
  PERTURB=$k nice -n 10 timeout 200 ./shrink beam $S/nm180_c3xs3_b5_14.edges 170 10 20000 2 0.3 $seed pt$seed 0 50 2>/dev/null | grep "^SA n=170" | sed "s/^/seed=$seed k=$k /" >> out/pt_results.txt
done
echo DONE >> out/pt_results.txt
