#!/bin/sh
# (3,9) Haar from 257 (order 256 deferred: 56,092 groups), then (3,10) Haar; one thread.
cd "$(dirname "$0")/.."
nice -n 5 python3 allgroups.py 3 9 257 330 >> runs/allgroups_d3D9.log 2>&1
nice -n 5 python3 allgroups.py 3 10 401 460 > runs/allgroups_d3D10.log 2>&1
echo ALLDONE >> runs/allgroups_d3D10.log
