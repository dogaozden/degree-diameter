#!/bin/bash
# Haar graphs (dipole lifts) with haar_gen3 for the small cells the repo's Haar job lists never covered.
# Waits for the two (5,10) haar_gen3 pushes; then one cell after another (one core), each job time-limited.
cd "$(dirname "$0")/.."
B=/tmp/claude-0/-home-user-degree-diameter/ee2ddafa-df45-5cb8-b9ed-a65866641afb/scratchpad/haar_gen3
while pgrep -f "haar_gen3 5 10 1200" > /dev/null; do sleep 15; done
h() { python3 haar_cell.py "$@" --bin $B; }
h 3 10 401 430 --tag hc_d3D10 --top 12 --secs 120
h 3 9 254 275 --tag hc_d3D9 --top 12 --secs 120
h 6 5 343 365 --tag hc_d6D5 --top 12 --secs 180
h 5 9 13969 14300 --tag hc_d5D9 --top 10 --secs 600
h 4 10 5875 6050 --tag hc_d4D10 --top 10 --secs 400
h 5 8 4618 4760 --tag hc_d5D8 --top 10 --secs 400
h 5 7 1556 1620 --tag hc_d5D7 --top 10 --secs 300
h 4 9 2486 2580 --tag hc_d4D9 --top 10 --secs 300
h 4 8 1093 1140 --tag hc_d4D8 --top 10 --secs 300
