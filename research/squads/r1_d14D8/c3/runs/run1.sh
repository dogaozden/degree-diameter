#!/bin/bash
cd /home/user/degree-diameter/research/squads/r1_d14D8/c3
# q=3, m=24, all sources exact per move, matchings fixed
timeout 900 nice -n 10 ./sa init_q3_m24.txt runs/q3_m24.txt 6000 2.0 0.2 364 1 0.0 1456 2 1000 1000 > runs/q3_m24.log 2>&1
echo "q3 done $?" >> runs/status.txt
# q=5, m=25, sampled K=64 per move, exact every 1000 moves
timeout 900 nice -n 10 ./sa init_q5_m25.txt runs/q5_m25.txt 8000 2.0 0.2 64 1 0.0 23436 2 1000 200 > runs/q5_m25.log 2>&1
echo "q5 done $?" >> runs/status.txt
