#!/bin/bash
# A3: RANDORB=30 screen of the three SL groups with ORBIT="5 2 1", run one after another inside one gate slot.
unset THREADS
H=/home/user/degree-diameter/research/structured/haar_sym
cd /home/user/degree-diameter/research/squads/d11D10-r1/A3 || exit 1
for g in "61 331" "41 1091" "71 211"; do
  set -- $g
  echo "=== sl $1 x Z$2"
  env ORBIT="5 2 1" RANDORB=30 "$H" 11 10 1 1 8 /dev/null sl $1 $2
  echo "rc=$?"
done
