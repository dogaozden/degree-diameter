#!/bin/bash
# usage: screen.sh START END  (lines of k3plus.txt, 5 s each, seed 1)
B=/tmp/claude-0/-home-user-degree-diameter/dc6fd85c-f533-550d-af33-040d4dcb67e6/scratchpad/bin
cd /home/user/degree-diameter/research/squads/b48/r3/d01
sed -n "$1,$2p" k3plus.txt | while read m k r; do
  res=$(THREADS=1 timeout 120 nice -n 10 $B/haar_fast 4 9 5 1 8 scr_${m}_${k}.txt meta $m $k $r 1 2>&1 | grep RESULT)
  echo "$m $k $r $res" >> screen_results.txt
done
