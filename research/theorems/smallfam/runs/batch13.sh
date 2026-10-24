#!/bin/sh
# is DGQ's (3,10) = 800 a Haar graph of a group of order 400, or a 2+2 lift over a group of order 200?
cd "$(dirname "$0")/.."
nice -n 5 python3 allgroups.py 3 10 400 400 --tag _400 > runs/allgroups_d3D10_400.log 2>&1
nice -n 5 python3 allgroups.py 3 10 200 200 --base bases/b22.txt --abmax 152 --tag _200 > runs/lift_b22_D10_200.log 2>&1
