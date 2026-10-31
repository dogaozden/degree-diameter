#!/bin/bash
# r3b batch17: longer D5 runs at n = 170 (standard sigma 2^8 1, alpha 4), PV 0.8, 150 s each, seeds 22 and 23
cd /home/user/degree-diameter/research/squads/handsoff-37/r3b
mkdir -p out/b17
for seed in 22 23; do
  timeout 100 nice -n 10 ./symbo out/b10/d5_170c/grp.txt out/b10/d5_170c/start.txt 150 $seed out/b17/d5_s$seed 40 10 0.7 1 1000000 0.8 2> out/b17/d5_s$seed.log
  echo "D5 170 150s seed=$seed PV=0.8: $(tail -1 out/b17/d5_s$seed.log) $(../bin/score37 out/b17/d5_s${seed}_best.edges | tail -1)"
done
echo BATCH17_DONE
