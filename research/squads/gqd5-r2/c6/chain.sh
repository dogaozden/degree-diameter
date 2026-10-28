#!/bin/bash
cd /home/user/degree-diameter/research/squads/gqd5-r2/c6
timeout 900 nice -n 10 python3 sa7.py targ 1 8 4000 1 1.0 b1_s8 > log_b1_s8.txt 2>&1
timeout 900 nice -n 10 python3 sa7.py targ 2 4 3000 1 1.0 b2_a2_s4 > log_b2_a2_s4.txt 2>&1
timeout 900 nice -n 10 python3 sa7.py targ 4 4 3000 1 1.0 b4_a4_s4 > log_b4_a4_s4.txt 2>&1
timeout 900 nice -n 10 python3 baseline7.py > baseline_out.txt 2>&1
echo CHAIN_DONE >> baseline_out.txt
