#!/bin/bash
cd /home/user/degree-diameter/research/squads/beyond-small/r1/c10
while read n k r u v N; do
  timeout 60 nice -n 10 ./tabu $n $k $r $u $v 0 7 20 12 1500 found/g${N}_${n}_${k}_${r}_${u}_${v}_f0.txt 2>/dev/null
done
