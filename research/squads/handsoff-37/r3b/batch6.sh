#!/bin/bash
# r3b batch6: Z15 = Z5 x Z3 at n=170 (Z3 part non-free: 2 fixed + five 3-cycles per side, alpha 1), symbo, 70 s
cd /home/user/degree-diameter/research/squads/handsoff-37/r3b
for seed in 1 2; do
  timeout 100 nice -n 10 ./symbo out/z15/grp.txt out/z15/start.txt 70 $seed out/z15/s$seed 40 10 0.7 1 1000000 0.5 2> out/z15/s$seed.log
  echo "z15 170 seed=$seed: $(tail -1 out/z15/s$seed.log) $(../bin/score37 out/z15/s${seed}_best.edges | tail -1)"
done
echo BATCH6_DONE
