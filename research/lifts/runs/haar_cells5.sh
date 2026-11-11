#!/bin/bash
# Haar lane for the small cells that never had a haar_cell sweep (01:50), replacing the (5,9) lane of
# haar_cells4.sh (its candidates sat at cost 2-4). One core, 5 h limit; windows start just above the table.
cd "$(dirname "$0")/.."
B=/tmp/claude-0/-home-user-degree-diameter/ee2ddafa-df45-5cb8-b9ed-a65866641afb/scratchpad/haar_gen3
h() { python3 haar_cell.py "$@" --bin $B --seeds 1 --top 8 --secs 300; }
export -f h; export B
timeout 5h bash -c "h 10 5 2001 2060 --tag hc_d10D5; h 5 7 1556 1620 --tag hc_d5D7; h 7 7 11719 11900 --tag hc_d7D7 --screen 100; h 4 9 2486 2580 --tag hc_d4D9; h 4 8 1093 1140 --tag hc_d4D8" > runs/hc5_lane_small.out 2>&1
