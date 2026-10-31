#!/bin/bash
# r3b batch14: D5 with PV 0.8 at n=180 (M 5, K 18, alpha 4, sigma 2^9 both sides; seeds 14, 15) and at n=170 with K 80 (seed 16, 120 s)
cd /home/user/degree-diameter/research/squads/handsoff-37/r3b
mkdir -p out/b14
D5_180=$(python3 -c "print(','.join(['2']*9))")
for seed in 14 15; do
  mkdir -p out/b14/d5_180
  python3 mkgroup.py 5 18 4 "$D5_180" "$D5_180" out/b14/d5_180/grp.txt out/b14/d5_180/start_$seed.txt $seed > out/b14/d5_180/mk_$seed.log 2>&1
  timeout 100 nice -n 10 ./symbo out/b14/d5_180/grp.txt out/b14/d5_180/start_$seed.txt 90 $seed out/b14/d5_180/s$seed 40 10 0.7 1 1000000 0.8 2> out/b14/d5_180/s$seed.log
  echo "D5 180 seed=$seed PV=0.8: $(tail -1 out/b14/d5_180/s$seed.log) $(../bin/score37 out/b14/d5_180/s${seed}_best.edges | tail -1)"
done
timeout 100 nice -n 10 ./symbo out/b10/d5_170c/grp.txt out/b10/d5_170c/start.txt 110 16 out/b14/d5_170k80 80 10 0.7 1 1000000 0.8 2> out/b14/d5_170k80.log
echo "D5 170 K=80 seed=16 PV=0.8: $(tail -1 out/b14/d5_170k80.log) $(../bin/score37 out/b14/d5_170k80_best.edges | tail -1)"
echo BATCH14_DONE
