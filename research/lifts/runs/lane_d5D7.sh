#!/bin/bash
# (5,7) long anneals (03:30), on the core of the stopped (5,10) second pass: the 300 s sweep left N = 1,560 and 1,582
# at cost 2 (six runs). Re-anneal the 10 best-screened candidates with new seeds and 1,200 s each; 4 h limit.
cd "$(dirname "$0")/.."
B=/tmp/claude-0/-home-user-degree-diameter/ee2ddafa-df45-5cb8-b9ed-a65866641afb/scratchpad/haar_gen3
timeout 4h python3 haar_cell.py 5 7 1556 1620 --tag hc_d5D7 --top 10 --secs 1200 --seeds 1 --seed0 2 --resume --bin $B > runs/lane_d5D7.out 2>&1
