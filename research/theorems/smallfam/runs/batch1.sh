#!/bin/sh
# (4,7) Haar over all groups, orders 421..546 (resumes; orders with > 20,000 groups are skipped and logged)
cd "$(dirname "$0")/.."
nice -n 5 python3 allgroups.py 4 7 421 546 --maxplan 2e7 >> runs/allgroups_d4D7.log 2>&1
