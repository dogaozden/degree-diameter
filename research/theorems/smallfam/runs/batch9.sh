#!/bin/sh
# 3+3 cubic bases lifted over every group, (3,9) orders 85..110 (6N >= 510 > 506); |G^ab| <= generic lattice bound
cd "$(dirname "$0")/.."
for b in 0 1 2; do
  case $b in 0) ab=133;; 1) ab=149;; 2) ab=121;; esac
  nice -n 5 python3 allgroups.py 3 9 85 110 --base bases/b33_$b.txt --cycles 4 --abmax $ab --threads 1 >> runs/lift_b33_$b.log 2>&1
done
