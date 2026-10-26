#!/bin/bash
# screen: one gated salift run per line of screen.list (D=10, 12 s each, seed 1)
cd /home/user/degree-diameter/research/squads/own-small/r1/c3
while read p N id; do
  out=scr/p${p}_g${N}_${id}.log
  D=10 /home/user/degree-diameter/research/squads/own-small/tools/slot.sh 40 /home/user/degree-diameter/research/squads/own-small/tools/bin/salift $p groups/g${N}.txt $id 1 12 5 0.5 sol/p${p}_g${N}_${id}.sol > $out 2>&1
  echo "$p $N $id $(head -1 $out | cut -c1-60) | $(grep 'end best' $out) | $(grep -c FOUND $out)" >> screen_results.txt
done < screen.list
echo SCREEN_DONE >> screen_results.txt
