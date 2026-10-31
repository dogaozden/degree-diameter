#!/bin/bash
# r3b batch15: F20 at n=180 (M 5, K 18, alpha 2, sigma 4,4,4,4,2 both sides) with PV 0.8, seeds 17, 18, 90 s each
cd /home/user/degree-diameter/research/squads/handsoff-37/r3b
mkdir -p out/b15
F20_180=$(python3 -c "print('4,4,4,4,2')")
for seed in 17 18; do
  python3 mkgroup.py 5 18 2 "$F20_180" "$F20_180" out/b15/grp_$seed.txt out/b15/start_$seed.txt $seed > out/b15/mk_$seed.log 2>&1
  timeout 100 nice -n 10 ./symbo out/b15/grp_$seed.txt out/b15/start_$seed.txt 90 $seed out/b15/f20_180_s$seed 40 10 0.7 1 1000000 0.8 2> out/b15/f20_180_s$seed.log
  echo "F20 180 seed=$seed PV=0.8: $(tail -1 out/b15/f20_180_s$seed.log) $(../bin/score37 out/b15/f20_180_s${seed}_best.edges | tail -1)"
done
echo BATCH15_DONE
