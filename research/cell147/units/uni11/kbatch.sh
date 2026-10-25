#!/bin/bash
# subgroup-orbit cliques: lines "q C ORDER SIDE SEED SECS"
cd /home/user/degree-diameter/research/cell147/units/uni11
xargs -P 2 -L 1 sh -c '
  n=k$0_$2$3_s$4
  python3 grpperm.py $0 $2 $3 $4 jperms/$n.txt > logs/$n.grp 2>&1 || { echo "$n: no group"; exit 0; }
  Q=$0 nice -n 5 timeout 400 ./orbitclique_q ../../data/E$0.map jperms/$n.txt $5 1 flags/$n.flags 2> logs/$n.log > /dev/null
  echo "$n: $(grep -o "trace-2 elements: [0-9]*" logs/$n.grp) | $(grep -o "orbit sizes.*" logs/$n.grp | cut -c1-60) | $(grep -o "best: .*points" logs/$n.log)"'
