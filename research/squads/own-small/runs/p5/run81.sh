#!/bin/bash
# 5+5 joint base+voltage annealing (salift_s, D=10) over every group of order 81, 3 in parallel, 120 s each, 2 seeds.
cd /home/user/degree-diameter/research/squads/own-small/runs/p5
for seed in 1 2; do
  for id in $(seq 1 15); do
    while [ $(jobs -r | wc -l) -ge 3 ]; do sleep 1; done
    D=10 ../../tools/bin/salift_s 5 g81.txt $id $seed 120 10 0.3 s81_${id}_$seed.sol > s81_${id}_$seed.log 2>&1 &
  done
done
wait; echo DONE81 > done81
