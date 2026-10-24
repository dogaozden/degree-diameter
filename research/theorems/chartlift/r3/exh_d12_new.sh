#!/bin/bash
# Exhaustive Haar scan for (12,5), the 17 chart classes (S4-orbits of the 348 labelled singular sets) that r3/exh_d12.sh
# did not cover (r3/flags43_orbit_reps.txt, tag NEW), over the same 88 groups of order 65..81.  Output r3/exh_d12_new.log.
W=/tmp/claude-0/-home-user-degree-diameter/8e7a80fa-6b09-58cb-8199-8d05845bbe55/scratchpad/w
grep NEW r3/flags43_orbit_reps.txt | while read fl tag; do
  while read name file; do
    out=$(EXH=1 nice -n 12 $W/ctrl_exh bases4/k4r1_000.txt $file $fl 1 1 | grep -E "EXH (r=|first_zero)" | tr '\n' ' ')
    echo "$(basename $fl .flags) $name $out"
  done < r3/groups_65_81.txt
done
