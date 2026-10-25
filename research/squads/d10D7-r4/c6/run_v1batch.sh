#!/bin/bash
cd /home/user/degree-diameter/research/squads/d10D7-r4/c6
H=/home/user/degree-diameter/research/d10D7/hex/hex_q5.bin
: > v1batch_summary.txt
for s in $(seq 100 119); do
  timeout 30 nice -n 10 ./ls6_v1 $H points 4 $s V1_s$s > V1_s$s.log 2>&1
  echo "seed $s : $(grep FOUND V1_s$s.log | tail -1)" >> v1batch_summary.txt
done
echo DONE >> v1batch_summary.txt
