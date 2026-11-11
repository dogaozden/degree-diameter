#!/bin/bash
# (4,10) follow-up 2 (04:57): when followup_d4D10.sh finishes N = 6,301-6,600, replace its planned long re-anneals of
# N = 6,124-6,300 (6 x 1,200 s) by a broad pass (30 best-screened candidates, 400 s, one seed): at (5,7) the solving
# group ranked 22nd in the screening. 3 h limit.
cd "$(dirname "$0")/.."
LANE=$1
B=/tmp/claude-0/-home-user-degree-diameter/ee2ddafa-df45-5cb8-b9ed-a65866641afb/scratchpad/haar_gen3
killtree() { for c in $(pgrep -P $1); do killtree $c; done; kill $1 2>/dev/null; }
until grep -q "hc3_d4D10: done" runs/followup_d4D10.out; do sleep 15; done
killtree $LANE
timeout 3h python3 haar_cell.py 4 10 6124 6300 --tag hc2_d4D10 --top 30 --secs 400 --seeds 1 --resume --bin $B > runs/followup2_d4D10.out 2>&1
