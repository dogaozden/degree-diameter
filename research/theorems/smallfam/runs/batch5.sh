#!/bin/sh
cd "$(dirname "$0")/.."
nice -n 5 python3 allgroups.py 3 10 201 255 --base bases/b22.txt --abmax 152 --threads 1 > runs/lift_b22_D10.log 2>&1
