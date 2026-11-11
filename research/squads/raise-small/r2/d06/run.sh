#!/bin/bash
# usage: run.sh TAB SEED OUTNAME T0 [START]
cd /home/user/degree-diameter/research/squads/raise-small/r2/d06
S=/home/user/degree-diameter/research/frontier/raise_small/bin/salift_s
if [ -n "$5" ]; then export START=$5; fi
D=11 timeout 100 nice -n 10 $S ${P:-3} $1 1 $2 15 $4 0.3 $3.sol > $3.log 2>&1
echo "exit $?"; tail -2 $3.log; head -1 $3.sol.best 2>/dev/null
