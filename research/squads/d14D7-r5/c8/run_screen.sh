#!/bin/bash
# screening pass: all Frobenius-normalised subgroups of order 6..30, orbclq -t 6, one process at a time
cd /home/user/degree-diameter/research/squads/d14D7-r5/c8
for k in E6 H6 H4 E4; do
  timeout 900 nice -n 10 python3 frob.py $k --hi 30 --t 6 --seed 1 >> screen.log 2>&1
done
echo SCREEN_DONE >> screen.log
