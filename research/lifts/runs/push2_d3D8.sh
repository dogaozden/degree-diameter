#!/bin/bash
# second (3,8) push with the composite-modulus aff and aff3 families (added after push_d3D8 had built its job list)
cd "$(dirname "$0")/.."
while pgrep -f "tag push_d3D8 " > /dev/null || pgrep -f "tag push_d3D8$" > /dev/null; do sleep 15; done
python3 run_cell.py --delta 3 --D 8 --orders 290:400 --hs 1,2,3 --rich --screen 150 --top 10 --maxbases 3 --maxgroups 80 --secs 20 --budget 2400 --workers 2 --stop-on-solve --tag push2_d3D8
