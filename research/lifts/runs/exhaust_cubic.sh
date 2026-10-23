#!/bin/bash
# exhaustive scans (niced, one core): cubic cells over all 2+2 and 3+3 cubic bases and all rich groups of the order
cd "$(dirname "$0")/.."
while pgrep -f "d3D8_k33_exhaust.sh" > /dev/null; do sleep 10; done
python3 exhaust_cell.py --delta 3 --D 8 --orders 258:300 --hs 2,3 --tag ex_d3D8 --maxspace 2e7
python3 exhaust_cell.py --delta 3 --D 9 --orders 508:560 --hs 2,3 --tag ex_d3D9 --maxspace 6e7
python3 exhaust_cell.py --delta 3 --D 10 --orders 802:880 --hs 2,3 --tag ex_d3D10 --maxspace 1.5e8
