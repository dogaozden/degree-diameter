#!/bin/bash
cd /home/user/degree-diameter/research/squads/d10D7-r4/c6
H=/home/user/degree-diameter/research/d10D7/hex/hex_q5.bin
: > points_v3_summary.txt
# (a) intensify from the 72-point set
timeout 100 nice -n 10 ./ls6b $H points 60 11 P3_from72 points72.txt > P3_from72.log 2>&1
echo "from72 : $(grep -E 'FOUND|start file' P3_from72.log | tail -2 | tr '\n' ' ') | $(tail -1 P3_from72.log)" >> points_v3_summary.txt
# (b) multi-start short runs
for s in $(seq 20 39); do
  timeout 30 nice -n 10 ./ls6b $H points 3 $s P3_ms$s > P3_ms$s.log 2>&1
  echo "ms seed $s : $(grep FOUND P3_ms$s.log | tail -1)" >> points_v3_summary.txt
done
echo DONE >> points_v3_summary.txt
