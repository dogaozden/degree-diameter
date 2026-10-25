#!/bin/bash
# c1 (r4): run orbitclique (q = 11, 60 s CPU, seed 1) on each subgroup orbit system given as arguments (tags).
C=/home/user/degree-diameter/research/squads/d14D7-r4/c1
HEAVY=/home/user/degree-diameter/research/squads/bin/heavy.sh
MAP=/home/user/degree-diameter/research/cell147/data/E11.map
for t in "$@"; do
  $HEAVY 150 /home/user/degree-diameter/research/cell147/units/orbitclique $MAP $C/permH_$t.txt 60 1 $C/flags_$t.txt 2> $C/log_$t.txt
  echo "$t rc=$? $(grep '^best' $C/log_$t.txt)"
done
