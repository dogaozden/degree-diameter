#!/bin/sh
# (3,7): 3+3 and 4+4 cubic bases lifted over every group (6N, 8N > 168 and <= 254), |G^ab| <= lattice bound
cd "$(dirname "$0")/.."
for b in b33_0 b33_1 b33_2; do
  ab=$(python3 liftbound.py bases/$b.txt 7 | sed 's/.*<= //')
  nice -n 5 python3 allgroups.py 3 7 29 42 --base bases/$b.txt --cycles 4 --abmax $ab --threads 1 >> runs/lift_${b}_D7.log 2>&1
done
for b in b44_0 b44_1 b44_2 b44_3 b44_4 b44_5; do
  ab=$(python3 liftbound.py bases/$b.txt 7 | sed 's/.*<= //')
  nice -n 5 python3 allgroups.py 3 7 22 31 --base bases/$b.txt --cycles 5 --abmax $ab --threads 1 >> runs/lift_${b}_D7.log 2>&1
done
echo ALLDONE >> runs/lift_b44_5_D7.log
