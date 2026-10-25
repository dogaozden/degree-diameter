#!/bin/bash
# sequential short runs of the points search with different seeds (one process at a time)
cd /home/user/degree-diameter/research/squads/d10D7-r4/c6
H=/home/user/degree-diameter/research/d10D7/hex/hex_q5.bin
: > points_seed_summary.txt
for s in 3 4 5 6 7 8; do
  timeout 100 nice -n 10 ./ls6 $H points 25 $s P_s$s > P_s$s.log 2>&1
  best=$(grep "FOUND" P_s$s.log | tail -1)
  echo "seed $s : $best" >> points_seed_summary.txt
done
echo DONE >> points_seed_summary.txt
