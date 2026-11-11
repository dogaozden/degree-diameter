#!/bin/bash
# lns_g10.sh (round 5, card g10, side B): random small destroy (drop 3-6 orbits), regrow 90 s with growb (R=8000),
# keep the result if it has at least as many orbits. Seed base 11000. Stops after TIMEBOX seconds.
cd /home/user/degree-diameter/research/squads/beyond-small/r5/g10
G=/home/user/degree-diameter/research/squads/beyond-small/data/d16D5_n33792.edges
GROWB=/home/user/degree-diameter/research/squads/beyond-small/r3/e02/growb
B=cur_B.txt
TIMEBOX=2700
START=$(date +%s)
i=0
while [ $(( $(date +%s) - START )) -lt $TIMEBOX ]; do
  i=$((i+1))
  R=$((3 + RANDOM % 4))
  shuf $B | head -n -$R > fix_B.txt
  rm -f try_B.txt
  timeout 150 nice -n 10 $GROWB $G fix_B.txt try_B.txt 90 $((11000 + i*1000 + RANDOM % 1000)) 6 8000 > growb_last.out 2>&1
  a=$(wc -l < $B); b=$(wc -l < try_B.txt 2>/dev/null || echo 0)
  if [ "$b" -ge "$a" ] && [ "$b" -gt 0 ]; then cp try_B.txt $B; fi
  echo "$i drop $R: $a -> $b (best $(wc -l < $B)) t=$(( $(date +%s) - START ))" >> lns_g10.log
done
echo DONE best $(wc -l < $B) >> lns_g10.log
