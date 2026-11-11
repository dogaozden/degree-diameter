#!/bin/bash
# cdd.sh ITERS : conflict-directed destroy on side A (swapped ids). Blame table recomputed only when the packing changes.
cd "$(dirname "$0")"
G=../../data/Gswap.edges
GROW=../../r3/e02/growb
cp start_swap.txt cur.txt
best=$(wc -l < cur.txt)
cp cur.txt best_swap_$best.txt
echo "start $best" >> cdd.log
need=1
for i in $(seq 1 $1); do
  if [ $need = 1 ]; then
    BLAME_OUT=$PWD/blame.txt timeout 100 nice -n 10 ./growb_f02 $G cur.txt /dev/null 60 $((RANDOM)) 6 30000 > /dev/null 2> blame_$i.err
    need=0
  fi
  k=$((2 + RANDOM % 3))
  dropped=$(python3 pick.py blame.txt cur.txt $k fix_cur.txt)
  timeout 100 nice -n 10 $GROW $G fix_cur.txt try.txt 60 $((RANDOM)) 6 4000 > /dev/null 2> grow_$i.err
  a=$(wc -l < cur.txt); b=$(wc -l < try.txt 2>/dev/null || echo 0)
  if [ "$b" -ge "$a" ] && [ "$b" -gt 0 ]; then
    cp try.txt cur.txt; need=1
    if [ "$b" -gt "$best" ]; then best=$b; cp cur.txt best_swap_$b.txt; fi
  fi
  echo "$i k=$k dropped=[$dropped] $a -> $b  (cur $(wc -l < cur.txt), best $best, blame-top $(sort -k2 -gr blame.txt | head -1))" >> cdd.log
done
echo done >> cdd.log
