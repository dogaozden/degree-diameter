#!/bin/bash
# alpha sweep: ORBIT="2 4 0" on prod psl 7 sl 9 1, RANDORB=300 per conjugating element index
B=/tmp/claude-0/-home-user-degree-diameter/2744c2da-0db8-5a6f-87c3-01a128c9c95e/scratchpad/bin
cd /home/user/degree-diameter/research/squads/r3/c5/
: > alpha_sweep.txt
for I in $(cat alpha_idx.txt); do
  out=$(ALPHA=$I ORBIT="2 4 0" RANDORB=300 timeout 120 nice -n 10 $B/haar_sym 8 8 1 1 8 /dev/null prod psl 7 sl 9 1 2>&1)
  rnd=$(echo "$out" | grep "RANDORB d=" | head -1)
  mn=$(echo "$rnd" | grep -o " min=[0-9]*" | cut -d= -f2)
  if [ -z "$mn" ]; then echo "$I SKIP $(echo "$out" | tail -1)" >> alpha_sweep.txt; continue; fi
  fix=$(echo "$rnd" | grep -o " fix=[0-9]*" | cut -d= -f2)
  p1=$(echo "$rnd" | grep -o " p1=[0-9]*" | cut -d= -f2)
  med=$(echo "$rnd" | grep -o " median=[0-9]*" | cut -d= -f2)
  echo "$I fix=$fix min=$mn p1=$p1 median=$med" >> alpha_sweep.txt
done
