#!/bin/sh
# (4,7) Haar over all groups, orders 449..546, orders with more than 300 groups skipped (logged); order 448 left partial
cd "$(dirname "$0")/.."
nice -n 5 python3 allgroups.py 4 7 449 546 --maxplan 2e7 --maxgroups 300 >> runs/allgroups_d4D7.log 2>&1
