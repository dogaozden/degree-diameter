#!/bin/bash
# r3b batch5: seed sweep of F20 (Z5 x| Z4, alpha 2, sigma 4,4,2,2,2,2,1 both sides) at n=170, symbo, 70 s each
cd /home/user/degree-diameter/research/squads/handsoff-37/r3b
mkdir -p out/b5
for seed in 21 22 23 24 25 26; do
  timeout 100 nice -n 10 ./symbo out/f20_170/grp.txt out/b5/start_$seed.txt 70 $seed out/b5/s$seed 40 10 0.7 1 1000000 0.5 2> out/b5/s$seed.log
  echo "f20 170 seed=$seed: $(tail -1 out/b5/s$seed.log) $(../bin/score37 out/b5/s${seed}_best.edges | tail -1)"
done
echo BATCH5_DONE
