#!/bin/bash
# g04 (side A, card r5/g04): random small destroy with long repairs, from r5/startA_swap.txt.
# Drop 3-6 random orbits, regrow 90 s (growb R=8000, seed base 5000), keep if orbit count not lower.
cd "$(dirname "$0")"
G=../../data/Gswap.edges
GROWB=/home/user/degree-diameter/research/squads/beyond-small/r3/e02/growb
cp ../startA_swap.txt cur.txt
best=$(wc -l < cur.txt)
start=$(date +%s)
TIMEBOX=2640
it=0
while [ $(( $(date +%s) - start )) -lt $TIMEBOX ]; do
  it=$((it+1))
  R=$((3 + RANDOM % 4))
  shuf cur.txt | head -n -$R > fix.txt
  rm -f try.txt
  timeout 150 nice -n 10 $GROWB $G fix.txt try.txt 90 $((5000 + it*7919 + RANDOM % 1000)) 6 8000 > growb_last.log 2>&1
  b=$(wc -l < try.txt 2>/dev/null || echo 0)
  a=$(wc -l < cur.txt)
  if [ "$b" -ge "$a" ] && [ "$b" -gt 0 ]; then cp try.txt cur.txt; fi
  c=$(wc -l < cur.txt)
  if [ "$c" -gt "$best" ]; then
    best=$c
    awk '{for(i=1;i<=NF;i++) $i+=16896; print}' cur.txt > best_sideA_$c.txt
  fi
  echo "it $it t=$(( $(date +%s) - start ))s drop $R: $a -> $b (cur $c, best $best)" >> lns_g04.log
done
echo DONE best $best >> lns_g04.log
