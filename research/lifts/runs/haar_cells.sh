#!/bin/bash
# Haar graphs (dipole lifts) with haar_gen3 for the small cells the repo's Haar job lists never covered.
# Waits for the two (5,10) haar_gen3 pushes; then one cell after another (one core), each job time-limited.
cd "$(dirname "$0")/.."
B=/tmp/claude-0/-home-user-degree-diameter/ee2ddafa-df45-5cb8-b9ed-a65866641afb/scratchpad/haar_gen3

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
# green cells (documentation runs: the size law predicts failure)
h 10 5 2001 2060 --tag hc_d10D5 --top 6 --secs 300
h 7 7 11719 11900 --tag hc_d7D7 --top 5 --secs 300 --screen 100
# (10,8) not run here: the candidate generator enumerates metacyclic groups per order and is too slow at N ~ 6e5
# (5,10) above our 91,728 (resumed after the container restart): direct haar_gen3 runs, 1200 s each
for job in "sl 11 35" "sl 13 22"; do for s in 1 2; do
  t=d5D10_$(echo $job | tr ' ' '_')_r$s
  timeout 1300 $B 5 10 1200 $s 8 sols/haar/$t.txt $job > runs/haar_$t.log 2>&1
  grep -q "full diameter check: OK" runs/haar_$t.log && echo "SOLVED (5,10) $job seed $s -> sols/haar/$t.txt"
done; done
