#!/bin/bash
# g02 (side A, big destroy): drop R=8..12 orbits from best_A.txt (swapped ids), regrow with 2 growb seeds of 40 s
# (seed base 3000), keep the best if its orbit count >= the current one. Improvements are also written in global ids.
cd "$(dirname "$0")"
G=/home/user/degree-diameter/research/squads/beyond-small/data/Gswap.edges
GB=/home/user/degree-diameter/research/squads/beyond-small/r3/e02/growb
a=$(wc -l < best_A.txt)
R=$((8 + RANDOM % 5))
shuf best_A.txt | head -n -$R > fix_g02.txt
bestb=0; bestf=""
for s in 1 2; do
  seed=$((3000 + RANDOM))
  timeout 100 nice -n 10 $GB $G fix_g02.txt try_g02_$s.txt 40 $seed 6 4000 > /dev/null 2>&1
  b=$(wc -l < try_g02_$s.txt 2>/dev/null || echo 0)
  echo "seed $seed: $b" >> trace_g02.txt
  if [ "$b" -gt "$bestb" ]; then bestb=$b; bestf=try_g02_$s.txt; fi
done
if [ "$bestb" -ge "$a" ] && [ -n "$bestf" ]; then
  cp $bestf best_A.txt
  if [ "$bestb" -gt "$a" ]; then
    awk '{for(i=1;i<=NF;i++)$i+=16896; print}' best_A.txt > best_sideA_$bestb.txt
  fi
fi
echo "drop $R: $a -> $bestb (best now $(wc -l < best_A.txt))" >> lns_g02.log
tail -1 lns_g02.log
