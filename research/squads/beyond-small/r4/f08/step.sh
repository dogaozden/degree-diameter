#!/bin/bash
# One big destroy (drop R=8..12 orbits from best_B.txt), regrow with 2 growb seeds of 40 s, keep the best if >= best.
cd "$(dirname "$0")"
G=/home/user/degree-diameter/research/squads/beyond-small/data/d16D5_n33792.edges
GB=/home/user/degree-diameter/research/squads/beyond-small/r3/e02/growb
[ -f best_B.txt ] || cp ../startB.txt best_B.txt
a=$(wc -l < best_B.txt)
R=$((8 + RANDOM % 5))
shuf best_B.txt | head -n -$R > fix_f08.txt
bestb=0
for s in 1 2; do
  seed=$((RANDOM + 1))
  timeout 100 nice -n 10 $GB $G fix_f08.txt try_f08_$s.txt 40 $seed 6 4000 > /dev/null 2>&1
  b=$(wc -l < try_f08_$s.txt 2>/dev/null || echo 0)
  echo "seed $seed: $b" >> trace_f08.txt
  if [ "$b" -gt "$bestb" ]; then bestb=$b; bestf=try_f08_$s.txt; fi
done
if [ "$bestb" -ge "$a" ]; then cp $bestf best_B.txt; fi
echo "drop $R: $a -> $bestb (best now $(wc -l < best_B.txt))" >> lns_f08.log
tail -1 lns_f08.log
