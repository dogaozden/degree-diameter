#!/bin/bash
# step.sh MODE(big|small) IT : one destroy-and-regrow iteration on side A (swapped ids), keeps result if not worse.
cd /home/user/degree-diameter/research/squads/beyond-small/r4/f04
G=/home/user/degree-diameter/research/squads/beyond-small
GR=$G/r3/e02/growb
EDGES=$G/data/Gswap.edges
MODE=$1; IT=$2
if [ "$MODE" = big ]; then R=$((8 + RANDOM % 5)); SECS=38; NS=2; else R=$((2 + RANDOM % 4)); SECS=55; NS=1; fi
cur=$(wc -l < cur.txt)
shuf cur.txt | head -n -$R > fix_$IT.txt
best=0; bestf=""
for s in $(seq 1 $NS); do
  seed=$RANDOM
  timeout 100 nice -n 10 $GR $EDGES fix_$IT.txt try_${IT}_${s}.txt $SECS $seed 6 4000 > g_${IT}_$s.log 2>&1
  n=$(wc -l < try_${IT}_${s}.txt 2>/dev/null || echo 0)
  if [ "$n" -gt "$best" ]; then best=$n; bestf=try_${IT}_${s}.txt; fi
done
if [ "$best" -ge "$cur" ] && [ -n "$bestf" ]; then cp "$bestf" cur.txt; acc=ACC; else acc=rej; fi
echo "$IT $MODE drop $R: $cur -> $best $acc (cur now $(wc -l < cur.txt))" >> log.txt
