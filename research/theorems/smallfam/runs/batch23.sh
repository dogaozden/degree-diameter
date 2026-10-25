#!/bin/sh
# (4,8): 4-regular 2+2 base lifts over SmallGroups of orders 547..570 (4N > 2184), annealing screen, 30 s per base
cd "$(dirname "$0")/.."
nice -n 5 python3 lscreen.py bases/b22d4_22.txt 8 547 570 --secs 30 --abmin 2 --abmax 48 > runs/lscreen_b22d4_22.log 2>&1
nice -n 5 python3 lscreen.py bases/b22d4_31.txt 8 547 570 --secs 30 --abmin 2 --abmax 48 > runs/lscreen_b22d4_31.log 2>&1
