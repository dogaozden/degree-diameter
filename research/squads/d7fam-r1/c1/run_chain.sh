#!/bin/bash
cd /home/user/degree-diameter/research/squads/d7fam-r1/c1
COMMON="--init /tmp/claude-0/-home-user-degree-diameter/0ecf9576-c77c-5462-b736-5bb1ddd9e678/scratchpad/w/sq/state_k12_r6c3.npz --secs 360 --pool 20000 --m 8 --sample 150 --rfile /tmp/claude-0/-home-user-degree-diameter/0ecf9576-c77c-5462-b736-5bb1ddd9e678/scratchpad/w/sq/R_q11.npy --hex /tmp/claude-0/-home-user-degree-diameter/0ecf9576-c77c-5462-b736-5bb1ddd9e678/scratchpad/w/sq/hex_q11.bin --sfile /tmp/claude-0/-home-user-degree-diameter/0ecf9576-c77c-5462-b736-5bb1ddd9e678/scratchpad/w/sq/S_q11.npy"
timeout 900 nice -n 15 python3 mirror_sa5.py 21 run_c62_T03 $COMMON --cmax 62 --T 0.3 > log_c62_T03.txt 2>&1
timeout 900 nice -n 15 python3 mirror_sa5.py 22 run_c62_T015 $COMMON --cmax 62 --T 0.15 > log_c62_T015.txt 2>&1
timeout 900 nice -n 15 python3 mirror_sa5.py 23 run_c70_T03 $COMMON --cmax 70 --T 0.3 > log_c70_T03.txt 2>&1
echo CHAIN_DONE > chain_done.txt
