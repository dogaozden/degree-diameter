#!/bin/bash
# r3b batch11: F20 at 170 with DIFFERENT sigma cycle types on the two sides (alpha 2): A = 4,4,2,2,2,2,1 and B = 4,4,4,2,2,1
# (and the reverse), symbo, 90 s, seeds 41 and 42
cd /home/user/degree-diameter/research/squads/handsoff-37/r3b
mkdir -p out/b11
run() { # tag cA cB seed
  local tag=$1 ca=$2 cb=$3 seed=$4
  mkdir -p out/b11/$tag
  python3 mkgroup.py 5 17 2 "$ca" "$cb" out/b11/$tag/grp.txt out/b11/$tag/start.txt $seed > out/b11/$tag/mk.log 2>&1 || { echo "mk fail $tag"; return; }
  timeout 100 nice -n 10 ./symbo out/b11/$tag/grp.txt out/b11/$tag/start.txt 90 $seed out/b11/$tag/s$seed 40 10 0.7 1 1000000 0.5 2> out/b11/$tag/s$seed.log
  echo "$tag sA=$ca sB=$cb seed=$seed: $(tail -1 out/b11/$tag/s$seed.log) $(../bin/score37 out/b11/$tag/s${seed}_best.edges | tail -1)"
}
run mixAB 4,4,2,2,2,2,1 4,4,4,2,2,1 41
run mixBA 4,4,4,2,2,1 4,4,2,2,2,2,1 42
echo BATCH11_DONE
