#!/bin/bash
# usage: screen.sh SECONDS SEED < lines "N m k r"; appends to screen_log.txt
B=/tmp/claude-0/-home-user-degree-diameter/dc6fd85c-f533-550d-af33-040d4dcb67e6/scratchpad/bin
D=/home/user/degree-diameter/research/squads/b48/r1/c03
SEC=$1; SEED=$2
while read N m k r; do
  out=$(THREADS=1 timeout 120 nice -n 10 $B/haar_fast 4 8 $SEC $SEED 8 $D/out_${m}_${k}_${r}.txt meta $m $k $r 1 2>&1 | grep RESULT)
  echo "$N $m $k $r :: $out" >> $D/screen_log.txt
done
