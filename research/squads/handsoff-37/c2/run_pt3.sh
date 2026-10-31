#!/bin/bash
cd /home/user/degree-diameter/research/squads/handsoff-37/c2
S=../shared/seeds
for seed in $(seq 300 359); do
  k=$(( seed % 2 + 1 ))
  if [ $(( seed % 2 )) -eq 0 ]; then SEED=$S/nm180_c30_b31.edges; TAG=pc; else SEED=$S/nm180_c3xs3_b5_14.edges; TAG=pd; fi
  PERTURB=$k nice -n 10 timeout 200 ./shrink beam $SEED 170 10 20000 2 0.3 $seed ${TAG}$seed 0 50 2>/dev/null | grep "^SA n=170" | sed "s/^/src=$TAG seed=$seed k=$k /" >> out/pt3_results.txt
done
echo DONE >> out/pt3_results.txt
