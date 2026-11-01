#!/bin/bash
cd /home/user/degree-diameter/research/frontier/raise_small
setsid nohup tools/scanlift.sh 13 4 runs/g13_469_560_k12.txt 60 runs/B13 1 > runs/B13c.out 2>&1 < /dev/null &
setsid nohup tools/scanlift.sh 14 3 runs/g14_p3_1171_1300_k12.txt 100 runs/A3 1 > runs/A3b.out 2>&1 < /dev/null &
sleep 2
for p in $(pgrep -f "tools/scanlift.sh 1[34] "); do echo -7 > /proc/$p/autogroup; done
