#!/bin/bash
# Batch for sat_q3.py (degree q+3). Runs 4 jobs at a time; one result line per job in q3_results.txt.
# Order: baselines first (should be SAT), then one and two extra vertices beyond the conic clones.
cd "$(dirname "$0")"
jobs=(
  "5 6 6 300"            # baseline: as many new points/lines as conic clones, all free
  "5 6 6 300 --gadget"
  "5 7 7 600 --gadget"   # one more of each
  "5 7 6 600 --gadget"
  "5 7 7 600 --gadget --clones"
  "5 8 8 900 --gadget --clones"
  "7 9 9 900 --gadget --clones"
  "7 10 9 900 --gadget --clones"
  "7 10 10 1200 --gadget --clones"
  "4 6 6 300"            # q even: hyperoval baseline is 6 + 6
  "4 7 7 600 --gadget"
  "9 11 11 1200 --gadget --clones"
)
printf '%s\n' "${jobs[@]}" | sed 's/ *#.*//' | xargs -P 4 -I{} sh -c 'python3 sat_q3.py {} >> q3_results.txt 2>&1'
echo "BATCH DONE" >> q3_results.txt
