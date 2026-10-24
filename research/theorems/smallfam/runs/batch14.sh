#!/bin/sh
# 3+3 cubic bases lifted over every group, (3,8) orders 49..84 (6N > 288, our record); |G^ab| <= lattice bound
cd "$(dirname "$0")/.."
for b in 0 1 2; do
  ab=$(python3 liftbound.py bases/b33_$b.txt 8 | sed 's/.*<= //')
  nice -n 5 python3 allgroups.py 3 8 49 84 --base bases/b33_$b.txt --cycles 4 --abmax $ab --threads 1 >> runs/lift_b33_${b}_D8.log 2>&1
done
