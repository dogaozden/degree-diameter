#!/bin/bash
# run2.sh TABLE ID SEED OUTNAME [START] -- p = 2 chunk (cubic 2+2 base), killed by timeout 105; .best survives
cd /home/user/degree-diameter/research/squads/beyond14/r2/d02
S=/home/user/degree-diameter/research/frontier/beyond14/ownsmall/salift_s
if [ -n "$5" ]; then ST="START=$5"; else ST="X=1"; fi
timeout 105 nice -n 10 env THREADS=1 D=14 $ST $S 2 $1 $2 $3 300 10 0.3 $4.sol > $4.log 2>&1
echo "exit=$? best:"; head -1 $4.sol.best 2>/dev/null; tail -2 $4.log 2>/dev/null
