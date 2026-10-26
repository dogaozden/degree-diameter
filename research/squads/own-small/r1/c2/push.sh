#!/bin/bash
cd /home/user/degree-diameter/research/squads/own-small/r1/c2
T=/home/user/degree-diameter/research/squads/own-small/tools
for p in "g104_0003 3 11" "g105_0001 0 12" "g108_0031 5 13"; do
  set -- $p
  $T/bin/flift bases/b4_$2.txt groups/bin/$1.bin 3 10 90 $3 8 work/push_$1_b$2_s$3 2>&1 | grep RESULT >> work/push.log
done
