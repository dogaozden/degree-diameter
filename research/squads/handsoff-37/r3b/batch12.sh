#!/bin/bash
# r3b batch12: plain SA (r2f symloc: orbit 2-switches, same-side cost, T 40 -> 4) on F20 at n=170, 90 s, seeds 1 and 2
cd /home/user/degree-diameter/research/squads/handsoff-37/r3b
mkdir -p out/b12
for seed in 1 2; do
  timeout 100 nice -n 10 ../r2f/symloc out/f20_170/grp.txt out/f20_170/start.txt $((90*25000)) 40 4 90 $seed out/b12/sa_s$seed 2> out/b12/sa_s$seed.log
  echo "F20 170 SA seed=$seed: $(tail -1 out/b12/sa_s$seed.log) $(../bin/score37 out/b12/sa_s${seed}_best.edges | tail -1)"
done
echo BATCH12_DONE
