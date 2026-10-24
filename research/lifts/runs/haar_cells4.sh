#!/bin/bash
# Haar queue, part 4 (01:45, after the container restart at 01:29 killed parts 3 and the hc2/hc4 sweeps).
# Four single-threaded lanes (4 cores), each under a 5 h limit. --resume reuses the logged screening and skips
# the runs already logged; the second pass of each lane re-anneals the best unsolved orders above our record with
# new seeds and a longer budget.
cd "$(dirname "$0")/.."
B=/tmp/claude-0/-home-user-degree-diameter/ee2ddafa-df45-5cb8-b9ed-a65866641afb/scratchpad/haar_gen3
h() { python3 haar_cell.py "$@" --bin $B; }
export -f h; export B
lane() { timeout 5h bash -c "$1" > runs/$2.out 2>&1; }
lane "h 5 8 4618 4760 --tag hc_d5D8 --top 10 --secs 400 --resume; h 5 8 4761 4900 --tag hc2_d5D8 --top 10 --secs 600" hc4_lane_d5D8 &
lane "h 5 10 47501 48500 --tag hc4_d5D10 --top 12 --secs 900 --seeds 1 --resume; h 5 10 47737 48500 --tag hc4_d5D10 --top 8 --secs 1800 --seeds 1 --seed0 2 --resume" hc4_lane_d5D10 &
lane "h 4 10 5995 6300 --tag hc2_d4D10 --top 12 --secs 400 --resume; h 4 10 5995 6300 --tag hc2_d4D10 --top 8 --secs 1200 --seeds 1 --seed0 3 --resume" hc4_lane_d4D10 &
lane "h 5 9 14422 14700 --tag hc2_d5D9 --top 8 --secs 1500 --seeds 1 --seed0 2 --resume" hc4_lane_d5D9 &
wait
