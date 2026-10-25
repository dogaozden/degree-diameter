#!/bin/bash
cd /home/user/degree-diameter/research/squads/d10D7-r4/c6
H=/home/user/degree-diameter/research/d10D7/hex/hex_q5.bin
: > points_v2_summary.txt
for s in 3 4 5; do
  timeout 100 nice -n 10 ./ls6 $H points 25 $s P2_s$s > P2_s$s.log 2>&1
  echo "seed $s : $(grep FOUND P2_s$s.log | tail -1)" >> points_v2_summary.txt
done
echo DONE >> points_v2_summary.txt
