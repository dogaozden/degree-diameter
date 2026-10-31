#!/bin/bash
# deep tabu on one group file for several seeds. usage: deep.sh ORDER ID BASE(a1|a2|a3) SECS SEED0 NSEEDS
C1=/home/user/degree-diameter/research/squads/handsoff-65/c1
S=/home/user/degree-diameter/research/squads/handsoff-65/shared
o=$1; id=$2; a=$3; SECS=$4; s0=$5; n=$6
G=$C1/tabs/sg_${o}_${id}.txt
mkdir -p $C1/sols
for ((k=0;k<n;k++)); do
  seed=$((s0+k))
  sol=$C1/sols/s${o}_${id}_${a}_${seed}.sol
  r=$(INIT=random SECS=$SECS SEED=$seed timeout $((SECS+60)) nice -n 10 $S/tabu $C1/bases/$a.base $G $sol 2>/dev/null | grep RESULT)
  c=$(echo "$r" | awk '{print $3}')
  printf '%s\t%s\t%s\tseed%s\t%s\t%s\n' "$o" "$id" "$a" "$seed" "${c:-NA}" "$(date -u +%H:%M)" >> $C1/deep.tsv
  if [ "$c" = "0" ]; then
    python3 $S/export_lift.py $sol $G $C1/sols/e${o}_${id}_${a}_${seed}.edges >/dev/null 2>&1
    $S/check.sh $C1/sols/e${o}_${id}_${a}_${seed}.edges >> $C1/deep.tsv 2>&1
  fi
  [ "${c:-99}" -gt 6 ] && rm -f $sol
done
