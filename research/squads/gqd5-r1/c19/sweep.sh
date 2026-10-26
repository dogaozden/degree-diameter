#!/bin/bash
cd /home/user/degree-diameter/research/squads/gqd5-r1/c19
for s in 2 4 8; do
  timeout 1500 nice -n 10 python3 anneal.py 2 $s 25000 $((10+s)) 1.0 2>&1 | grep -E "FINAL|start"
done
