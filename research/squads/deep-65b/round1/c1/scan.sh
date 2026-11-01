#!/bin/bash
# usage: scan.sh SECS SEED   (foreground; runs c1 on pending non-abelian groups from todo.txt, appends to raw.txt,
# starts no new group after ~85 s of this call)
D=/home/user/degree-diameter/research/squads/deep-65b/round1/c1
G=/home/user/degree-diameter/research/squads/deep-65b/groups
SECS=$1; SEED=$2
START=$(date +%s)
touch $D/raw.txt
while read ord id; do
  if grep -q "^$ord $id $SEED " $D/raw.txt; then continue; fi
  el=$(( $(date +%s) - START ))
  if [ $el -gt 85 ]; then break; fi
  name=$(sed 's/ |Aut|.*//' $G/sg_${ord}_${id}.name)
  line=$($D/c1 $G/sg_${ord}_${id}.tab $SEED $SECS)
  best=$(echo "$line" | sed 's/.* best=\([0-9]*\) .*/\1/')
  tb=$(echo "$line" | sed 's/.* t_best=\([0-9.]*\) .*/\1/')
  echo "$ord $id $SEED $best $tb $name" >> $D/raw.txt
done < $D/todo.txt
echo "done-call: $(wc -l < $D/raw.txt) raw lines; pending: $(awk -v s=$SEED '{print}' $D/todo.txt | wc -l) total"
