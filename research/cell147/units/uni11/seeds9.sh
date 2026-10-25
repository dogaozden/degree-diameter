#!/bin/bash
cd /home/user/degree-diameter/research/cell147/units/uni11
C6=/home/user/degree-diameter/research/squads/d14D7-r4/c6
for s in $(seq 1 50); do
  r=$(nice -n 5 $C6/orbitclique9 $C6/E9.map jperms/id9.txt 5 $s flags/ils9_s$s.flags 2>&1 | grep "^best" | awk '{print $4}')
  echo "$s $r"
done
