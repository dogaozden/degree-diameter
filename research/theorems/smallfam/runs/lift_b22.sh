#!/bin/sh
# 2+2 cubic base ((2,1),(1,2)) lifted over every group of the order (GAP SmallGroups), x up to Aut(G); 2 threads.
cd "$(dirname "$0")/.."
nice -n 5 python3 allgroups.py 3 7 43 63 --base bases/b22.txt --threads 2 > runs/lift_b22_D7.log 2>&1
nice -n 5 python3 allgroups.py 3 8 73 127 --base bases/b22.txt --threads 2 > runs/lift_b22_D8.log 2>&1
nice -n 5 python3 allgroups.py 3 9 127 170 --base bases/b22.txt --threads 2 > runs/lift_b22_D9.log 2>&1
nice -n 5 python3 allgroups.py 3 10 201 255 --base bases/b22.txt --threads 2 > runs/lift_b22_D10.log 2>&1
echo ALLDONE >> runs/lift_b22_D10.log
