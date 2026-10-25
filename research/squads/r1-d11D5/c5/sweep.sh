#!/bin/bash
cd /home/user/degree-diameter/research/squads/r1-d11D5/c5
for m in 14 12 10 8; do
  for seed in 1 2; do
    timeout 900 nice -n 10 ./c5sa $m $seed 20000 16 3.0 /home/user/degree-diameter/research/squads/r1-d11D5/c5/run > log_m${m}_s${seed}.txt 2>&1
  done
done
echo SWEEP_DONE > sweep.done
