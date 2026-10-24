#!/bin/sh
# second (4,8) screen: orders 1150..1200 (<= 400 groups per order), 5 <= |G/G'| <= 48
cd "$(dirname "$0")/.."
nice -n 5 python3 screen.py 4 8 1150 1200 --secs 20 --seeds 1 --maxgroups 400 --abmin 5 --abmaxorder 48 --tag _b > runs/screen_d4D8_b.log 2>&1
