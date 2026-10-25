#!/bin/bash
# Exhaustive Haar scan for (12,5): every voltage choice (one voltage fixed to e) for each (4,3) chart class and each
# group of order 65..81 that r3/mkgroups.py builds.  Output: r3/exh_d12.log ("class group EXH ... min_cost zero_count").
W=/tmp/claude-0/-home-user-degree-diameter/8e7a80fa-6b09-58cb-8199-8d05845bbe55/scratchpad/w
for c in 0 1 5 2 3 4 6; do
  while read name file; do
    out=$(EXH=1 nice -n 10 $W/ctrl_exh bases4/k4r1_000.txt $file r3/k4q3_diag_cls$c.flags 1 1 | grep -E "EXH (r=|first_zero)" | tr '\n' ' ')
    echo "cls$c $name $out"
  done < r3/groups_65_81.txt
done
