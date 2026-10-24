#!/bin/bash
# usage: run_seed.sh TAG SEED SECS GROUP... N
B=/tmp/claude-0/-home-user-degree-diameter/2744c2da-0db8-5a6f-87c3-01a128c9c95e/scratchpad/bin
TAG=$1; SEED=$2; SECS=$3; shift 3
cd /home/user/degree-diameter/research/squads
ORBIT="3 2 2" timeout 1000 nice -n 10 $B/haar_sym 8 9 $SECS $SEED 8 r4/c1/${TAG}_s${SEED}.txt "$@" > r4/c1/${TAG}_s${SEED}.log 2>&1
echo "EXIT $?" >> r4/c1/${TAG}_s${SEED}.log
