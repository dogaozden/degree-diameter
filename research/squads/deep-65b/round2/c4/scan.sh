#!/bin/bash
# usage: scan.sh SECS SEED TODO   (foreground; one line per run appended to raw.txt; skips runs already in raw.txt;
# starts no new run after ~85 s of this call so the call stays under 110 s)
D=/home/user/degree-diameter/research/squads/deep-65b/round2/c4
G=$D/tabs
T=/home/user/degree-diameter/research/squads/deep-65b/shared/tabu15
SECS=$1; SEED=$2; TODO=$3
START=$(date +%s)
mkdir -p $D/edges
touch $D/raw.txt
while read ord id; do
  if grep -q "^$ord $id $SEED $SECS " $D/raw.txt; then continue; fi
  el=$(( $(date +%s) - START ))
  if [ $el -gt 85 ]; then break; fi
  name=$(sed 's/ abelian=.*//' $G/sg_${ord}_${id}.name)
  line=$(timeout 105 nice -n 15 $T $G/sg_${ord}_${id}.tab $SEED $SECS $D/edges/e_${ord}_${id}_s${SEED}.edges)
  best=$(echo "$line" | sed 's/.* best=\([0-9]*\) .*/\1/')
  tb=$(echo "$line" | sed 's/.* t_best=\([0-9.]*\) .*/\1/')
  echo "$ord $id $SEED $SECS $best $tb $name" >> $D/raw.txt
done < $TODO
echo "call done: raw lines $(wc -l < $D/raw.txt); elapsed $(( $(date +%s) - START ))s"
