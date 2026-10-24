#!/bin/bash
cd /home/user/degree-diameter/research/squads/r2/c8
B=/tmp/claude-0/-home-user-degree-diameter/2744c2da-0db8-5a6f-87c3-01a128c9c95e/scratchpad/bin
i=0
for g in "psl 41 8" "sl 19 40" "psl 19 80" "psl 43 7"; do
  i=$((i+1))
  tag=t1_$(echo $g | tr ' ' '_')
  ORBIT="2 4 1" timeout 400 nice -n 10 $B/haar_sym 9 8 150 $i 8 $tag.txt $g > $tag.log 2>&1
done
echo ALLDONE > triage1.done
