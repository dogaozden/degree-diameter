#!/bin/bash
# f01 (side A): destroy-and-repair with long repairs. Drop 3-6 random Z22-orbits, regrow 90 s with growb R=8000,
# keep the result if it has at least as many orbits. Works on the side-swapped graph (ids < 16896).
cd "$(dirname "$0")"
G=../../data/Gswap.edges
GROWB=/home/user/degree-diameter/research/squads/beyond-small/r3/e02/growb
cp ../startA_swap.txt cur.txt
best=$(wc -l < cur.txt)
start=$(date +%s)
it=0
while [ $(( $(date +%s) - start )) -lt 2280 ]; do
  it=$((it+1))
  R=$((3 + RANDOM % 4))
  shuf cur.txt | head -n -$R > fix.txt
  $GROWB $G fix.txt try.txt 90 $RANDOM 6 8000 > growb_last.log 2>&1
  b=$(wc -l < try.txt 2>/dev/null || echo 0)
  a=$(wc -l < cur.txt)
  if [ "$b" -ge "$a" ] && [ "$b" -gt 0 ]; then cp try.txt cur.txt; fi
  c=$(wc -l < cur.txt)
  if [ "$c" -gt "$best" ]; then
    best=$c
    awk '{for(i=1;i<=NF;i++) $i+=16896; print}' cur.txt > best_sideA_$c.txt
  fi
  echo "it $it t=$(( $(date +%s) - start ))s drop $R: $a -> $b (cur $c, best $best)" >> lns_f01.log
done
echo DONE >> lns_f01.log
