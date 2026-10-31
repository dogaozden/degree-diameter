#!/bin/bash
# r3b batch7: other sigma cycle types for F20 (Z5 x| Z4, alpha 2) at n=170, symbo, seed 1, 70 s each
cd /home/user/degree-diameter/research/squads/handsoff-37/r3b
mkdir -p out/b7
run() {
  local name=$1 sg=$2
  mkdir -p out/b7/$name
  python3 mkgroup.py 5 17 2 "$sg" "$sg" out/b7/$name/grp.txt out/b7/$name/start.txt 1 > out/b7/$name/mk.log 2>&1 || { echo "mk fail $name sigma=$sg"; return; }
  timeout 100 nice -n 10 ./symbo out/b7/$name/grp.txt out/b7/$name/start.txt 70 1 out/b7/$name/s1 40 10 0.7 1 1000000 0.5 2> out/b7/$name/s1.log
  echo "$name sigma=$sg: $(tail -1 out/b7/$name/s1.log) $(../bin/score37 out/b7/$name/s1_best.edges | tail -1)"
}
run f20_s44422_1 "4,4,4,2,2,1"
run f20_s4442111111 "4,4,4,1,1,1,1,1"
run f20_s44222111 "4,4,2,2,2,1,1,1"
echo BATCH7_DONE
