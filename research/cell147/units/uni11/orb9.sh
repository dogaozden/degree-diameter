#!/bin/bash
# longer orbit-clique runs on card c6's best order-5 isometries of E9 (one at a time)
cd /home/user/degree-diameter/research/cell147/units/uni11
C6=/home/user/degree-diameter/research/squads/d14D7-r4/c6
for spec in "s7_m2_d5 2" "s8_m27_d5 2" "s7_m2_d5 3" "s8_m35_d5 3" "s8_m6_d5 4"; do
  set -- $spec
  r=$(nice -n 5 $C6/orbitclique9 $C6/E9.map $C6/perms/$1.txt 60 $2 flags/orb9_$1_s$2.flags 2>&1 | grep "^best")
  echo "$1 seed $2: $r"
done
