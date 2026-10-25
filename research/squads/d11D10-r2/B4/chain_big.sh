#!/bin/bash
# B4: one gate slot, one checker on the 157.8M-vertex file. Usage: chain_big.sh CHECKER SECS_NOTE
B=/home/user/degree-diameter/research/squads/d11D10-r2/B4
T=/home/user/degree-diameter/research/squads/d11D10-r2/tools
c=$1
env -u THREADS python3 -I $B/runtimed.py $B/logs/big_${c}.log $T/$c $B/big_psl_243_11_r11_s1.txt
echo "$c big rc=$?" >> $B/logs/chain_big.status
