#!/bin/bash
# card c4: after screening, take the 3 best (group, base) pairs and run 120 s tabu runs with two new seeds each
cd /home/user/degree-diameter/research/squads/s384r3/c4
B=/tmp/claude-0/s65/research/s65/bases
while ! grep -q SCREEN2_DONE screen2.out 2>/dev/null; do sleep 3; done
# top 3 by cost (ties: first seen)
awk -F'|' '{ match($0, /best [0-9]+/); c=substr($0, RSTART+5, RLENGTH-5); split($1, a, " "); print c, a[1], a[2], a[3] }' screen.log | sort -n -k1,1 -s | head -3 > top3.txt
cat top3.txt
while read c N ID bl; do
  bk=${bl#b22_}
  for SEED in 2 3; do
    out=$(INIT=random D=5 SECS=120 SEED=$SEED timeout 900 ./bin/tabu $B/b22_${bk}.txt groups/sg_${N}_${ID}.txt sols/long_${N}_${ID}_b${bk}_s${SEED}.sol 2>long_${N}_${ID}_b${bk}_s${SEED}.err | grep RESULT)
    echo "$N $ID $bl seed $SEED screen $c | $(cat groups/sg_${N}_${ID}.name) | $out" | tee -a long.log
  done
done < top3.txt
echo LONG_DONE >> long.log
