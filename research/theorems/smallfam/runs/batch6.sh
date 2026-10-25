#!/bin/sh
# which group of order 1092 carries Loz's (4,8) = 2184 (if it is a Haar graph)?
cd "$(dirname "$0")/.."
nice -n 10 python3 allgroups.py 4 8 1092 1092 --maxplan 3e7 --gap-timeout 900 --tag _1092 > runs/allgroups_d4D8_1092.log 2>&1
