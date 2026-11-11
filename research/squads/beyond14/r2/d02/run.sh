#!/bin/bash
# run.sh ID SEED OUTNAME [START]  -- one salift_s chunk, killed by timeout 105 (the .best file survives)
cd /home/user/degree-diameter/research/squads/beyond14/r2/d02
S=/home/user/degree-diameter/research/frontier/beyond14/ownsmall/salift_s
if [ -n "$4" ]; then
  timeout 105 nice -n 10 env THREADS=1 D=14 START="$4" $S 4 tabs.txt $1 $2 300 10 0.3 $3.sol > $3.log 2>&1
else
  timeout 105 nice -n 10 env THREADS=1 D=14 $S 4 tabs.txt $1 $2 300 10 0.3 $3.sol > $3.log 2>&1
fi
echo "exit=$? best:"; head -1 $3.sol.best 2>/dev/null; tail -2 $3.log 2>/dev/null
