#!/bin/bash
# Haar queue, part 2 (replaces the rest of haar_cells.sh at 20:47): most promising cell first by mu at the table order.
cd "$(dirname "$0")/.."
B=/tmp/claude-0/-home-user-degree-diameter/ee2ddafa-df45-5cb8-b9ed-a65866641afb/scratchpad/haar_gen3
h() { python3 haar_cell.py "$@" --bin $B; }
h 5 9 13969 14300 --tag hc_d5D9 --top 10 --secs 600
# (5,10) above our 91,728: direct haar_gen3 runs, 1200 s each
for job in "sl 11 35" "sl 13 22"; do for s in 1 2; do
  t=d5D10_$(echo $job | tr ' ' '_')_r$s
  timeout 1300 $B 5 10 1200 $s 8 sols/haar/$t.txt $job > runs/haar_$t.log 2>&1
  grep -q "full diameter check: OK" runs/haar_$t.log && echo "SOLVED (5,10) $job seed $s -> sols/haar/$t.txt"
done; done
h 4 10 5875 6050 --tag hc_d4D10 --top 10 --secs 400
h 5 8 4618 4760 --tag hc_d5D8 --top 10 --secs 400
h 5 7 1556 1620 --tag hc_d5D7 --top 10 --secs 300
h 4 9 2486 2580 --tag hc_d4D9 --top 10 --secs 300
h 4 8 1093 1140 --tag hc_d4D8 --top 10 --secs 300
h 10 5 2001 2060 --tag hc_d10D5 --top 6 --secs 300
h 7 7 11719 11900 --tag hc_d7D7 --top 5 --secs 300 --screen 100
