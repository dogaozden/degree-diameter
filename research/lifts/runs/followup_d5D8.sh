#!/bin/bash
# (5,8) follow-up (03:22): the small-cell lane (haar_cells5.sh) is stopped ((10,5), (5,7), (7,7), (4,9) sat at cost
# 2-44), and its core sweeps (5,8) N = 4,901-5,100 at once; after the haar_cells4.sh (5,8) lane finishes
# N = 4,761-4,900 (it solved 4,788), that core sweeps N = 5,101-5,300. 4 h limit each.
cd "$(dirname "$0")/.."
B=/tmp/claude-0/-home-user-degree-diameter/ee2ddafa-df45-5cb8-b9ed-a65866641afb/scratchpad/haar_gen3
timeout 4h python3 haar_cell.py 5 8 4901 5100 --tag hc3_d5D8 --top 10 --secs 600 --bin $B > runs/followup_d5D8.out 2>&1 &
until grep -q "hc2_d5D8: done" runs/hc4_lane_d5D8.out; do sleep 15; done
timeout 4h python3 haar_cell.py 5 8 5101 5300 --tag hc4_d5D8 --top 10 --secs 600 --bin $B > runs/followup2_d5D8.out 2>&1
wait
