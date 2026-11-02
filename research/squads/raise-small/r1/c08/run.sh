#!/bin/bash
# run.sh TABNAME P SECS SEED OUTSTEM [START]: one salift_s run (D=14), keeps OUTSTEM.sol.best; prints best line.
cd /home/user/degree-diameter/research/squads/raise-small/r1/c08
B=/home/user/degree-diameter/research/frontier/raise_small/bin
if [ -n "$6" ]; then export START="$6"; fi
D=14 timeout 100 nice -n 10 $B/salift_s $2 g_$1.tab 1 $4 $3 10 0.3 $5.sol > $5.log 2>&1
echo "run $1 p=$2 seed=$4 rc=$?"; grep -E "group|FOUND|end" $5.log | tail -3; head -1 $5.sol.best 2>/dev/null
