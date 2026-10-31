#!/bin/bash
cd /home/user/degree-diameter/research/squads/handsoff-37/r3d
for s in 101 102 103 104 105 106 107 108; do
  ./lift3d 17 10 $s 200 3 0.3 400000 out/bg_A10_$s - 4 > out/bg_A10_$s.log 2>&1
done
echo finished > out/bg_done.txt
