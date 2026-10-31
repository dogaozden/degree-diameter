#!/bin/bash
# r3b batch8: n = 180 (K = 18 base vertices per side, M = 5): D5 (alpha 4, sigma 2^9) and F20 (alpha 2, sigma 4,4,4,4,2), symbo 80 s
cd /home/user/degree-diameter/research/squads/handsoff-37/r3b
mkdir -p out/b8
run() { # name M K ALPHA SIGMA seed
  local name=$1 m=$2 k=$3 al=$4 sg=$5 seed=$6
  mkdir -p out/b8/$name
  python3 mkgroup.py $m $k $al "$sg" "$sg" out/b8/$name/grp.txt out/b8/$name/start.txt $seed > out/b8/$name/mk.log 2>&1 || { echo "mk fail $name seed=$seed"; return; }
  timeout 100 nice -n 10 ./symbo out/b8/$name/grp.txt out/b8/$name/start.txt 80 $seed out/b8/$name/s$seed 40 10 0.7 1 1000000 0.5 2> out/b8/$name/s$seed.log
  echo "$name n=$((2*k*m)) $(head -1 out/b8/$name/grp.txt) seed=$seed: $(tail -1 out/b8/$name/s$seed.log) $(../bin/score37 out/b8/$name/s${seed}_best.edges | tail -1)"
}
D5_180=$(python3 -c "print(','.join(['2']*9))")
F20_180=$(python3 -c "print('4,4,4,4,2')")
run d5_180 5 18 4 "$D5_180" 1
run f20_180 5 18 2 "$F20_180" 1
run d5_180 5 18 4 "$D5_180" 2
run f20_180 5 18 2 "$F20_180" 2
echo BATCH8_DONE
