#!/bin/bash
# Haar queue 6 (05:35). The container restarts every few hours (18:52, 01:29, 05:28) and kills every job, so every
# step uses --resume: re-running this script after a restart continues where the logs stop. Broad passes (many
# screened candidates, one seed, 400-900 s each), because at (5,7) the solving group ranked 22nd in the screening.
# Four lanes = 4 cores; each step has its own time limit.
cd "$(dirname "$0")/.."
B=/tmp/claude-0/-home-user-degree-diameter/ee2ddafa-df45-5cb8-b9ed-a65866641afb/scratchpad/haar_gen3
h() { local lim=$1; shift; timeout $lim python3 haar_cell.py "$@" --seeds 1 --resume --bin $B; }
laneA() {   # (4,10), record N = 6,123
  h 2h 4 10 6124 6300 --tag hc2_d4D10 --top 30 --secs 400
  h 2h 4 10 6301 6600 --tag hc3_d4D10 --top 30 --secs 400
  h 3h 4 10 6601 6900 --tag hc4_d4D10 --top 24 --secs 400
}
laneB() {   # (5,8), record N = 4,788
  h 3h 5 8 4901 5100 --tag hc3_d5D8 --top 24 --secs 400
  h 2h 5 8 4789 4900 --tag hc2_d5D8 --top 24 --secs 400
}
laneC() {   # (5,8) higher, then (5,9), record N = 14,421
  h 3h 5 8 5101 5300 --tag hc4_d5D8 --top 24 --secs 400
  h 4h 5 9 14422 14700 --tag hc2_d5D9 --top 24 --secs 600
}
laneD() {   # (5,7), record N = 1,560, then (5,10), record N = 47,736
  h 3h 5 7 1556 1620 --tag hc_d5D7 --top 30 --secs 400
  h 5h 5 10 47737 48500 --tag hc4_d5D10 --top 24 --secs 900
}
laneA > runs/q6_A.out 2>&1 &
laneB > runs/q6_B.out 2>&1 &
laneC > runs/q6_C.out 2>&1 &
laneD > runs/q6_D.out 2>&1 &
wait
