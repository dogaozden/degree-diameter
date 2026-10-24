#!/bin/bash
# anneal the 8 best alpha indices of prod psl 3 psl 7 8 (k=2 m=3 f=0), 120 s each, seed 1
B=/tmp/claude-0/-home-user-degree-diameter/2744c2da-0db8-5a6f-87c3-01a128c9c95e/scratchpad/bin
cd /home/user/degree-diameter/research/squads/r3/c6/anneal_a
for I in 7 111 1900 1228 1324 135 146 1894; do
  ALPHA=$I ORBIT="2 3 0" timeout 900 nice -n 10 $B/haar_sym 6 8 120 1 8 sol_$I.txt prod psl 3 psl 7 8 > log_$I.txt 2>&1
done
echo ALLDONE > done.flag
