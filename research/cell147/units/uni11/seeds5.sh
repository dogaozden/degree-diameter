#!/bin/bash
cd /home/user/degree-diameter/research/cell147/units/uni11
for s in $(seq 1 80); do
  r=$(Q=5 nice -n 5 ./orbitclique_q ../../data/E5.map jperms/id5.txt 2 $s flags/ils5_s$s.flags 2>&1 | grep "^best" | awk '{print $4}')
  echo "$s $r"
done
