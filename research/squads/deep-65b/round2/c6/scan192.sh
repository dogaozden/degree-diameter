#!/bin/bash
# usage: scan192.sh  (foreground; runs tabu15f on pending order-192 groups from todo192.txt, 2 seeds x 8 s each,
# appends "id seed best t_best name" to raw192.txt, starts no new group after 80 s of this call; hits to hits/)
D=/home/user/degree-diameter/research/squads/deep-65b/round2/c6
TAB=$D/tabs
touch $D/raw192.txt
START=$(date +%s)
while read id; do
  if grep -q "^$id 1 " $D/raw192.txt && grep -q "^$id 2 " $D/raw192.txt; then continue; fi
  el=$(( $(date +%s) - START ))
  if [ $el -gt 80 ]; then break; fi
  name=$(sed 's/ abelian=.*//' $TAB/sg_192_${id}.name)
  for seed in 1 2; do
    line=$($D/tabu15f $TAB/sg_192_${id}.tab $seed 8 $D/hits/e192_${id}_s${seed}.edges)
    best=$(echo "$line" | sed 's/.* best=\([0-9]*\) .*/\1/')
    tb=$(echo "$line" | sed 's/.* t_best=\([0-9.]*\) .*/\1/')
    echo "$id $seed $best $tb $name" >> $D/raw192.txt
    if [ "$best" = "0" ]; then echo "HIT id=$id seed=$seed" >> $D/hits/HITS.txt; fi
  done
done < ${TODO:-$D/todo192.txt}
echo "call done: $(awk '{print $1}' $D/raw192.txt | sort -u | wc -l) groups with results"
