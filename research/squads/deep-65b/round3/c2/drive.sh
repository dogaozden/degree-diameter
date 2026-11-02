#!/bin/bash
# usage: drive.sh BUDGET_MS   (resumable; round-robin over seeds 1..20 and the 10 order-180 groups; 10 s per run)
# starts a new run only if elapsed + 10.3 s <= BUDGET_MS; appends RES lines to raw.txt; keeps zeros in zeros/
C=/home/user/degree-diameter/research/squads/deep-65b/round3/c2
D=/home/user/degree-diameter/research/squads/deep-65b/groups
S=/home/user/degree-diameter/research/squads/deep-65b/shared
BUDGET=${1:-102000}
GRPS="14 2 33 22 28 1 8 20 16 19"
mkdir -p $C/zeros
touch $C/raw.txt
t0=$(date +%s%N)
for s in $(seq 1 20); do
  for g in $GRPS; do
    el=$(( ($(date +%s%N) - t0) / 1000000 ))
    if [ $(( el + 10300 )) -gt $BUDGET ]; then echo "budget reached at ${el} ms"; exit 0; fi
    if grep -q "ID=$g NAME=.* seed=$s best=" $C/raw.txt; then continue; fi
    name=$(sed 's/ |Aut|.*//' $D/sg_180_$g.name)
    line=$(timeout 100 nice -n 15 $C/tabu15f $D/sg_180_$g.tab $s 10 $C/zeros/e_180_${g}_s${s}.edges)
    echo "ORD=180 ID=$g NAME=$name | $line" >> $C/raw.txt
    best=$(echo "$line" | sed 's/.* best=\([0-9]*\) .*/\1/')
    echo "ID=$g seed=$s best=$best"
    if [ "$best" = "0" ]; then echo "ZERO ID=$g seed=$s -> $C/zeros/e_180_${g}_s${s}.edges"; fi
  done
done
echo "all done"
