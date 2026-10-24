#!/bin/sh
# Delta=3 Haar over all groups: (3,10) orders 401..460, then (3,9) orders 320..330 (resumes)
cd "$(dirname "$0")/.."
nice -n 5 python3 allgroups.py 3 10 401 460 >> runs/allgroups_d3D10.log 2>&1
nice -n 5 python3 allgroups.py 3 9 320 330 >> runs/allgroups_d3D9.log 2>&1
