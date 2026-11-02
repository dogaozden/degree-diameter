#!/bin/bash
# usage: run_group.sh ORDER ID SEED_FROM SEED_TO SECS   (foreground; one tabu15 run per seed; appends to raw.txt)
D=/home/user/degree-diameter/research/squads/deep-65b
C=$D/round2/c1
ORD=$1; ID=$2; S1=$3; S2=$4; SECS=$5
NAME=$(sed 's/ |Aut|.*//' $D/groups/sg_${ORD}_${ID}.name)
mkdir -p $C/zeros
for s in $(seq $S1 $S2); do
  line=$(timeout 100 nice -n 15 $D/shared/tabu15 $D/groups/sg_${ORD}_${ID}.tab $s $SECS $C/zeros/e_${ORD}_${ID}_s${s}.edges)
  echo "ORD=$ORD ID=$ID NAME=$NAME | $line" >> $C/raw.txt
  echo "$ORD $ID $s $(echo "$line" | sed 's/.* best=\([0-9]*\) .*/\1/') $(echo "$line" | sed 's/.* t_best=\([0-9.]*\) .*/\1/')"
done
