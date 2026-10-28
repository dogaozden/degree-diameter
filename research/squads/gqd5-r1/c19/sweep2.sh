#!/bin/bash
cd /home/user/degree-diameter/research/squads/gqd5-r1/c19
for rs in "2 16" "2 32" "3 8" "3 16" "2 64" "3 32"; do
  set -- $rs
  timeout 1200 nice -n 10 python3 -u anneal.py $1 $2 25000 $((30+$2)) 1.0 >> sweep2.log 2>&1
done
echo ALLDONE >> sweep2.log
