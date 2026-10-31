#!/bin/bash
cd /home/user/degree-diameter/research/squads/handsoff-65/c6
until grep -q "drop=5" pipe372.out 2>/dev/null; do sleep 5; done
for i in 12 10 8 11 13 6 3 4 5 7 1 9 14; do ./pipe.sh 351 $i 30; done > pipe351.out 2>&1
echo DONE351 >> pipe351.out
