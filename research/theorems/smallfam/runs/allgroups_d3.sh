#!/bin/sh
# Delta=3 Haar graphs over all groups (GAP SmallGroups), exhaustive up to Aut, orders just above the table.
cd "$(dirname "$0")/.."
nice -n 5 python3 allgroups.py 3 7 85 127 > runs/allgroups_d3D7.log 2>&1
nice -n 5 python3 allgroups.py 3 9 254 330 > runs/allgroups_d3D9.log 2>&1
nice -n 5 python3 allgroups.py 3 10 401 460 > runs/allgroups_d3D10.log 2>&1
echo ALLDONE >> runs/allgroups_d3D10.log
