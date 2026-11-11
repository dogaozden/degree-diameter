#!/bin/bash
# Haar queue, part 3 (21:15): wait for the running (5,9) sweep (pid 11191), push (5,9) higher, then the remaining cells.
cd "$(dirname "$0")/.."
B=/tmp/claude-0/-home-user-degree-diameter/ee2ddafa-df45-5cb8-b9ed-a65866641afb/scratchpad/haar_gen3
h() { python3 haar_cell.py "$@" --bin $B; }
while kill -0 11191 2>/dev/null; do sleep 15; done
h 5 9 14210 14700 --tag hc2_d5D9 --top 12 --secs 600 --seeds 1
h 4 10 5875 6050 --tag hc_d4D10 --top 10 --secs 400
h 5 8 4618 4760 --tag hc_d5D8 --top 10 --secs 400
h 5 7 1556 1620 --tag hc_d5D7 --top 10 --secs 300
h 4 9 2486 2580 --tag hc_d4D9 --top 10 --secs 300
h 4 8 1093 1140 --tag hc_d4D8 --top 10 --secs 300
h 10 5 2001 2060 --tag hc_d10D5 --top 6 --secs 300
h 7 7 11719 11900 --tag hc_d7D7 --top 5 --secs 300 --screen 100
