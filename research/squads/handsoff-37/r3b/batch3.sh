#!/bin/bash
# r3b batch3: F20 at n=170 (Z5 x| Z4), symbo2 with elite restarts, several seeds and sigma types
cd /home/user/degree-diameter/research/squads/handsoff-37/r3b
mkdir -p out/b3
run() { # name sigma seed STALL
  local name=$1 sg=$2 seed=$3 stall=$4
  mkdir -p out/b3/$name
  python3 mkgroup.py 5 17 2 "$sg" "$sg" out/b3/$name/grp.txt out/b3/$name/start.txt $seed > out/b3/$name/mk.log 2>&1 || { echo "mk fail $name"; return; }
  timeout 100 nice -n 10 ./symbo2 out/b3/$name/grp.txt out/b3/$name/start.txt 80 $seed out/b3/$name/s$seed 40 10 0.7 1 1000000 0.5 $stall 2> out/b3/$name/s$seed.log
  echo "$name sigma=$sg seed=$seed stall=$stall: $(tail -1 out/b3/$name/s$seed.log) $(../bin/score37 out/b3/$name/s${seed}_best.edges | tail -1)"
}
run f20a_s3 "4,4,2,2,2,2,1" 3 400
run f20b_s4 "4,4,4,4,1" 4 400
run f20a_s5 "4,4,2,2,2,2,1" 5 150
echo BATCH3_DONE
