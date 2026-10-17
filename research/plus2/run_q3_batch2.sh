#!/bin/bash
# Batch 2 for sat_q3.py: q = 7 with nothing fixed. Decides whether hats exist one degree up beyond q = 5.
cd "$(dirname "$0")"
jobs=(
  "7 8 8 900"             # baseline: 8 + 8 new vertices, all free (conic clones are one solution)
  "7 9 9 3000 --gadget"   # one more of each, all free
  "7 9 8 3000 --gadget"
  "7 9 9 3000"            # one more of each, no gadget
)
printf '%s\n' "${jobs[@]}" | sed 's/ *#.*//' | xargs -P 4 -I{} sh -c 'python3 sat_q3.py {} >> q3_results2.txt 2>&1'
echo "BATCH DONE" >> q3_results2.txt
