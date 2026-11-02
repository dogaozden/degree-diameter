#!/bin/bash
# usage: scan.sh   (foreground; runs the pending lines of todo.txt, "ORD ID SEED TABPATH", one tabu15 run each, SECS=8;
# skips lines already in raw.txt; starts no new run after ~88 s of this call; appends "ORD ID SEED BEST T_BEST" to raw.txt)
D=/home/user/degree-diameter/research/squads/deep-65b/round2/c5
BIN=/home/user/degree-diameter/research/squads/deep-65b/shared/tabu15
SECS=8
START=$(date +%s)
mkdir -p $D/out
touch $D/raw.txt
while read ord id seed tab; do
  if grep -q "^$ord $id $seed " $D/raw.txt; then continue; fi
  el=$(( $(date +%s) - START ))
  if [ $el -gt 88 ]; then break; fi
  line=$($BIN $tab $seed $SECS $D/out/e_${ord}_${id}_${seed}.edges < /dev/null)
  best=$(echo "$line" | sed 's/.* best=\([0-9]*\) .*/\1/')
  tb=$(echo "$line" | sed 's/.* t_best=\([0-9.]*\) .*/\1/')
  echo "$ord $id $seed $best $tb" >> $D/raw.txt
done < $D/todo.txt
echo "raw lines: $(wc -l < $D/raw.txt); todo lines: $(wc -l < $D/todo.txt); elapsed $(( $(date +%s) - START )) s"
