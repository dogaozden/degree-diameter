#!/bin/bash
cd /home/user/degree-diameter/research/cell147/units/uni11
for s in $(seq 5 60); do
  r=$(Q=7 nice -n 5 ./orbitclique_q ../../data/E7.map jperms/id7.txt 4 $s flags/ils7_s$s.flags 2>&1 | grep "^best" | awk '{print $4}')
  echo "$s $r"
done
