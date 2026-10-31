#!/bin/bash
# r3b batch18: D5 (alpha 4) with more fixed base vertices, PV 0.8, 90 s each:
# n=170: sigma 2^5 1^7 (seed 31), 2^4 1^9 (seed 32), 2^7 1^3 with another seed (34); n=180: 2^7 1^4 (seed 33)
cd /home/user/degree-diameter/research/squads/handsoff-37/r3b
mkdir -p out/b18
run() { # tag M K sigma seed
  local tag=$1 m=$2 k=$3 sg=$4 seed=$5
  mkdir -p out/b18/$tag
  python3 mkgroup.py $m $k 4 "$sg" "$sg" out/b18/$tag/grp.txt out/b18/$tag/start.txt $seed > out/b18/$tag/mk.log 2>&1 || { echo "mk fail $tag sigma=$sg"; return; }
  timeout 100 nice -n 10 ./symbo out/b18/$tag/grp.txt out/b18/$tag/start.txt 90 $seed out/b18/$tag/s$seed 40 10 0.7 1 1000000 0.8 2> out/b18/$tag/s$seed.log
  echo "$tag n=$((2*k*m)) sigma=$sg seed=$seed PV=0.8: $(tail -1 out/b18/$tag/s$seed.log) $(../bin/score37 out/b18/$tag/s${seed}_best.edges | tail -1)"
}
run d5_170_2to5 5 17 "2,2,2,2,2,1,1,1,1,1,1,1" 31
run d5_170_2to4 5 17 "2,2,2,2,1,1,1,1,1,1,1,1,1" 32
run d5_170_2to7b 5 17 "2,2,2,2,2,2,2,1,1,1" 34
run d5_180_2to7 5 18 "2,2,2,2,2,2,2,1,1,1,1" 33
echo BATCH18_DONE
