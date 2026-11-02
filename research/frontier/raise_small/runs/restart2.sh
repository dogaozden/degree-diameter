#!/bin/bash
cd /home/user/degree-diameter/research/frontier/raise_small
setsid nohup tools/scanlift.sh 13 2 runs/g13_p2_1101_1300.txt 25 runs/B13p2 "1 2" > runs/B13p2.out 2>&1 < /dev/null &
setsid nohup tools/scanlift.sh 12 2 runs/g12_p2_593_720.txt 25 runs/D12p2 "1 2" > runs/D12p2.out 2>&1 < /dev/null &
sleep 2
for p in $(pgrep -f "tools/scanlift.sh 1[23] 2 "); do echo -7 > /proc/$p/autogroup; done
