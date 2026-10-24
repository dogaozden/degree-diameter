#!/bin/sh
# validation: order 420 at (4,7) must contain Bond-Delorme's A5 x Z7
cd "$(dirname "$0")/.."
nice -n 5 python3 allgroups.py 4 7 420 420 --maxplan 2e7 --tag _420 > runs/allgroups_d4D7_420.log 2>&1
