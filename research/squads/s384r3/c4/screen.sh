#!/bin/bash
# card c4 screening: one short tabu run (random start, 15 s) per non-abelian group, bases rotated over b22_1..3
cd /home/user/degree-diameter/research/squads/s384r3/c4
B=/tmp/claude-0/s65/research/s65/bases
i=0
while read N ID; do
  i=$((i+1))
  [ -n "$FROM" ] && [ $i -lt $FROM ] && continue
  [ -n "$TO" ] && [ $i -gt $TO ] && break
  bk=$(( (i % 3) + 1 ))
  name=$(cat groups/sg_${N}_${ID}.name 2>/dev/null)
  out=$(INIT=random D=5 SECS=15 SEED=1 timeout 900 ./bin/tabu $B/b22_${bk}.txt groups/sg_${N}_${ID}.txt sols/scr_${N}_${ID}_b${bk}.sol 2>/dev/null | grep RESULT)
  echo "$N $ID b22_$bk | $name | $out" | tee -a screen.log
done < groups/list.txt
