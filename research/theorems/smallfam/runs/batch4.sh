#!/bin/sh
# 2+2 cubic base lifts over all groups at (3,9): orders 129..170 first, order 128 (2,328 two-groups) last
cd "$(dirname "$0")/.."
nice -n 5 python3 allgroups.py 3 9 129 170 --base bases/b22.txt --abmax 112 --threads 1 >> runs/lift_b22_D9.log 2>&1
nice -n 5 python3 allgroups.py 3 9 127 128 --base bases/b22.txt --abmax 112 --threads 1 >> runs/lift_b22_D9.log 2>&1
