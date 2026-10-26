#!/bin/bash
cd /home/user/degree-diameter/research/squads/gqd5-r1/c19
while kill -0 5532 2>/dev/null; do sleep 3; done
for rs in "3 8" "3 16"; do
  set -- $rs
  timeout 1200 nice -n 10 python3 -u anneal.py $1 $2 25000 $((40+$2)) 1.0 >> sweep3.log 2>&1
done
echo ALLDONE >> sweep3.log
