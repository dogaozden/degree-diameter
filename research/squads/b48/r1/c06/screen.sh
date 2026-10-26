#!/bin/bash
# Card c06 screen: haar_fast 4 8, 5 s per group, seed 1, non-faithful metacyclic groups (ord(r) proper divisor of k)
B=/tmp/claude-0/-home-user-degree-diameter/dc6fd85c-f533-550d-af33-040d4dcb67e6/scratchpad/bin
cd /home/user/degree-diameter/research/squads/b48/r1/c06
while read N m k r d; do
  out=out_${m}_${k}_${r}.txt
  line=$(THREADS=1 timeout 120 nice -n 10 $B/haar_fast 4 8 5 1 8 $out meta $m $k $r 1 2>&1 | grep RESULT | tail -1)
  echo "$N $m $k $r ord=$d :: $line"
done < "$1"
