#!/bin/bash
# twisted cyclic groups: lines "q C a m side secs"
cd /home/user/degree-diameter/research/cell147/units/uni11
xargs -P 2 -L 1 sh -c '
  n=tw$0_a$2_m$3$4
  python3 permq3.py $0 $1 $2 $3 $4 jperms/$n.txt > /dev/null 2>&1 || { echo "$n: perm failed"; exit 0; }
  Q=$0 nice -n 5 timeout 400 ./orbitclique_q ../../data/E$0.map jperms/$n.txt $5 1 flags/$n.flags 2> logs/$n.log > /dev/null
  echo "$n: $(grep -o "[0-9]* orbits ([0-9]* usable); sizes:.*" logs/$n.log | cut -c1-70) | $(grep -o "best: .*points" logs/$n.log)"'
