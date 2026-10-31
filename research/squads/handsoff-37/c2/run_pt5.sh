#!/bin/bash
cd /home/user/degree-diameter/research/squads/handsoff-37/c2
S=../shared/seeds
gcc -O3 -march=native -o /tmp/claude-0/-home-user-degree-diameter/a669333e-f5e2-51cb-8889-7c5fc1354b9d/scratchpad/shrink4 shrink.c -lm 2>/dev/null
B=/tmp/claude-0/-home-user-degree-diameter/a669333e-f5e2-51cb-8889-7c5fc1354b9d/scratchpad/shrink4
for seed in $(seq 440 459); do
  PERTURB=1 nice -n 10 timeout 200 $B beam $S/nm180_c30_b31.edges 170 10 20000 2 0.3 $seed pf$seed 0 50 2>/dev/null | grep "^SA n=170" | sed "s/^/src=pe seed=$seed k=1 /" >> out/pt5_results.txt
done
echo DONE >> out/pt5_results.txt
