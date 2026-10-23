#!/bin/bash
# second (3,8) push (after the container restart): all rich groups incl. composite-modulus aff and aff3, orders 296-400
cd "$(dirname "$0")/.."
python3 run_cell.py --delta 3 --D 8 --orders 296:400 --hs 1,2,3 --rich --screen 150 --top 10 --maxbases 3 --maxgroups 80 --secs 20 --budget 3000 --workers 1 --stop-on-solve --tag push2_d3D8
