#!/bin/bash
# (5,7) Haar lane (03:21; changed 04:05). The 300 s sweep left N = 1,560 and 1,582 at cost 2 (six runs); 1,200 s
# re-anneals of two of them (seed 2) also stopped at cost 2. Solutions elsewhere came from other groups of the same
# order, usually within minutes, so this lane now goes broad: the 30 best-screened candidates, 400 s each; 4 h limit.
cd "$(dirname "$0")/.."
B=/tmp/claude-0/-home-user-degree-diameter/ee2ddafa-df45-5cb8-b9ed-a65866641afb/scratchpad/haar_gen3
timeout 4h python3 haar_cell.py 5 7 1556 1620 --tag hc_d5D7 --top 30 --secs 400 --seeds 1 --resume --bin $B > runs/lane_d5D7.out 2>&1
