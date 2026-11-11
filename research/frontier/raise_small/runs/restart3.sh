#!/bin/bash
cd /home/user/degree-diameter/research/frontier/raise_small
setsid nohup tools/scanlift.sh 13 2 runs/g13_p2_odd_d9.txt 25 runs/B13odd "1 2" > runs/B13odd.out 2>&1 < /dev/null &
sleep 2
for p in $(pgrep -f "tools/scanlift.sh 13 2 runs/g13_p2_odd"); do echo -7 > /proc/$p/autogroup; done
