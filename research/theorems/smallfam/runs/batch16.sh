#!/bin/sh
# (4,8) annealing screen over SmallGroups of orders 1093..1200 (orders with > 400 groups skipped), 5 <= |G/G'| <= 48
cd "$(dirname "$0")/.."
nice -n 5 python3 screen.py 4 8 1093 1200 --secs 20 --seeds 1 --maxgroups 400 --abmin 5 --abmaxorder 48 > runs/screen_d4D8.log 2>&1
