#!/bin/bash
# d07 screen: haar_fast D=9, seed 1, K=8, 8 s per group, one process at a time
B=/tmp/claude-0/-home-user-degree-diameter/dc6fd85c-f533-550d-af33-040d4dcb67e6/scratchpad/bin
DIR=/home/user/degree-diameter/research/squads/b48/r3/d07
cd $DIR
while read -r spec; do
  tag=$(echo "$spec" | tr ' ' '_')
  line=$(THREADS=1 timeout 120 nice -n 10 $B/haar_fast 4 9 ${SECS:-8} ${SEED:-1} 8 $DIR/sol_$tag.txt $spec 2>&1 | grep RESULT)
  echo "$spec | $line"
done
