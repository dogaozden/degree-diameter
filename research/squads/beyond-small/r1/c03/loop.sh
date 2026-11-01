#!/bin/bash
cd /home/user/degree-diameter/research/squads/beyond-small/r1/c03
for i in $(seq 1 40); do timeout 100 nice -n 10 python3 hub_next.py $((i+1)) >> hub_loop.log 2>&1; done
touch DONE
