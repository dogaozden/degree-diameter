#!/bin/bash
# screen metacyclic groups with no central involution (cands.txt filtered k>=12, o>=3), every 3rd, haar_fast D=9, 4 s, seed 1
B=/tmp/claude-0/-home-user-degree-diameter/dc6fd85c-f533-550d-af33-040d4dcb67e6/scratchpad/bin
cd /home/user/degree-diameter/research/squads/b48/r4/h13
mkdir -p screen
awk '$3>=12 && $5>=3' cands.txt | awk 'NR%3==1' > screen/list.txt
: > screen/results.txt
while read N m k r o g; do
  out=screen/s_${m}_${k}_${r}.txt
  line=$(THREADS=1 timeout 120 nice -n 10 $B/haar_fast 4 9 4 1 8 $out meta $m $k $r 1 2>/dev/null | grep RESULT)
  best=$(echo "$line" | sed -n 's/.*best=\([0-9]*\).*/\1/p')
  echo "$N $m $k $r $o $g best=$best" >> screen/results.txt
done < screen/list.txt
