#!/bin/bash
# screen.sh PAIRS_TSV SECS NS TT SEED OUTTSV : one tabu run per (group, base) pair; appends RESULT lines to OUTTSV
H=/home/user/degree-diameter/research/squads/handsoff-49
W=$H/w12
PAIRS=$1; SECS=$2; NS=$3; TT=$4; SEED=$5; OUT=$6
mkdir -p $W/runs/screen
while IFS=$'\t' read -r G B; do
  [ -z "$G" ] && continue
  base=$W/bases/$B
  tag="${G}__${B%.txt}"
  nice -n 10 timeout 120 $W/wt12 $base $W/groups/$G.bin 9 $SECS $SEED $W/runs/screen/$tag $NS $TT > $W/logs/screen_$tag.out 2>/dev/null
  res=$(grep RESULT $W/logs/screen_$tag.out | head -1)
  n=$(echo "$res" | sed -n 's/.*n=\([0-9]*\).*/\1/p')
  cost=$(echo "$res" | sed -n 's/RESULT cost=\([0-9]*\).*/\1/p')
  it=$(echo "$res" | sed -n 's/.*iters=\([0-9]*\).*/\1/p')
  printf "%s\t%s\t%s\t%s\t%s\t%s\n" "$G" "$B" "$n" "$cost" "$it" "$SEED" >> $OUT
done < $PAIRS
