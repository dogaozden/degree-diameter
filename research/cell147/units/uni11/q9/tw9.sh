#!/bin/bash
# GF(9) twisted cyclic groups R^a (+) Y^m (one run at a time, low priority)
cd /home/user/degree-diameter/research/cell147/units/uni11/q9
C6=/home/user/degree-diameter/research/squads/d14D7-r4/c6
mkdir -p perms flags logs
for a in 0 1 2 3 4 5; do for m in 0 1 2 3 4 5; do for side in R L; do
  [ $a = 0 ] && [ $m = 0 ] && continue
  n=tw9_a${a}_m${m}${side}
  nice -n 10 python3 permq3_9.py $a $m $side perms/$n.txt > /dev/null 2>&1 || { echo "$n perm failed"; continue; }
  r=$(nice -n 10 timeout 120 $C6/orbitclique9 $C6/E9.map perms/$n.txt 6 1 flags/$n.flags 2>&1 | grep -E "^best|usable" | tr '\n' ' ' | cut -c1-160)
  echo "$n: $r"
done; done; done
echo SWEEPDONE
