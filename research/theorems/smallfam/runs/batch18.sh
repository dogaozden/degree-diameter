#!/bin/sh
# (3,8) Haar over all groups, N = 145..204 (2N > 288, our record); orders with > 2000 groups skipped
cd "$(dirname "$0")/.."
nice -n 5 python3 allgroups.py 3 8 145 204 --maxgroups 2000 > runs/allgroups_d3D8.log 2>&1
