#!/bin/bash
# r3b batch16: other involution cycle types for D5 (alpha 4) with PV 0.8, 90 s each:
# n=170 sigma 2^7 1^3 (seed 19) and 2^6 1^5 (seed 20); n=180 sigma 2^8 1^2 (seed 21)
cd /home/user/degree-diameter/research/squads/handsoff-37/r3b
mkdir -p out/b16
run() { # tag M K sigma seed
  local tag=$1 m=$2 k=$3 sg=$4 seed=$5
  mkdir -p out/b16/$tag
  python3 mkgroup.py $m $k 4 "$sg" "$sg" out/b16/$tag/grp.txt out/b16/$tag/start.txt $seed > out/b16/$tag/mk.log 2>&1 || { echo "mk fail $tag"; return; }
  timeout 100 nice -n 10 ./symbo out/b16/$tag/grp.txt out/b16/$tag/start.txt 90 $seed out/b16/$tag/s$seed 40 10 0.7 1 1000000 0.8 2> out/b16/$tag/s$seed.log
  echo "$tag n=$((2*k*m)) sigma=$sg seed=$seed PV=0.8: $(tail -1 out/b16/$tag/s$seed.log) $(../bin/score37 out/b16/$tag/s${seed}_best.edges | tail -1)"
}
run d5_170_2to7 5 17 "2,2,2,2,2,2,2,1,1,1" 19
run d5_170_2to6 5 17 "2,2,2,2,2,2,1,1,1,1,1" 20
run d5_180_2to8 5 18 "2,2,2,2,2,2,2,2,1,1" 21
echo BATCH16_DONE
