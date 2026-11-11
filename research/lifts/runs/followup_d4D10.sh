#!/bin/bash
# (4,10) follow-up (01:55): when the first pass of the haar_cells4.sh (4,10) lane ends, stop that lane (its second
# pass would re-anneal orders below the new record N = 6,123) and run a fresh window above 6,300, then long
# re-anneals of the unsolved orders 6,124-6,300. 4 h limit.
cd "$(dirname "$0")/.."
LANE=$1
B=/tmp/claude-0/-home-user-degree-diameter/ee2ddafa-df45-5cb8-b9ed-a65866641afb/scratchpad/haar_gen3
killtree() { for c in $(pgrep -P $1); do killtree $c; done; kill $1 2>/dev/null; }
until grep -q "hc2_d4D10: done" runs/hc4_lane_d4D10.out; do sleep 15; done
killtree $LANE
h() { python3 haar_cell.py "$@" --bin $B; }
export -f h; export B
timeout 4h bash -c "h 4 10 6301 6600 --tag hc3_d4D10 --top 12 --secs 400; h 4 10 6124 6300 --tag hc2_d4D10 --top 6 --secs 1200 --seeds 1 --seed0 3 --resume" > runs/followup_d4D10.out 2>&1
