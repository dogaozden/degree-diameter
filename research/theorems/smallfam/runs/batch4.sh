#!/bin/sh
# 2+2 cubic base lifts over all groups: (3,9) N = 127..170 and (3,10) N = 201..255, |G^ab| <= generic bound
cd "$(dirname "$0")/.."
nice -n 5 python3 allgroups.py 3 9 127 170 --base bases/b22.txt --abmax 112 --threads 1 > runs/lift_b22_D9.log 2>&1
