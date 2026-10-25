#!/bin/bash
# step 2 chain: one joint run at a time (SECS=150 CPU, seed 1; wall-time guard: screen runs showed ~2.3x wall/CPU)
cd /home/user/degree-diameter/research/squads/d12D5-r1/c5
./run2.sh Z3xZ8R2 150 1
./run2.sh Dic6 150 1
./run2.sh SL23 150 1
echo CHAIN_DONE >> joint/summary.txt
