#!/bin/bash
# tabu restarted from a saved low-cost solution (INIT=sol), with occasional kicks. usage: restart.sh SOL GROUP BASE SECS SEED0 N
C1=/home/user/degree-diameter/research/squads/handsoff-65/c1; S=/home/user/degree-diameter/research/squads/handsoff-65/shared
SOL=$1; G=$2; B=$3; SECS=$4; s0=$5; n=$6; tag=$(basename $SOL .sol)
mkdir -p $C1/sols
for ((k=0;k<n;k++)); do
  seed=$((s0+k)); out=$C1/sols/r_${tag}_${seed}.sol
  r=$(INIT=sol KICK=3 STALL=800 SECS=$SECS SEED=$seed timeout $((SECS+60)) nice -n 10 $S/tabu $SOL $G $out 2>/dev/null | grep RESULT)
  c=$(echo "$r" | awk '{print $3}')
  printf 'restart\t%s\t%s\tseed%s\t%s\t%s\n' "$tag" "$B" "$seed" "${c:-NA}" "$(date -u +%H:%M)" >> $C1/deep.tsv
  if [ "$c" = "0" ]; then python3 $S/export_lift.py $out $G $C1/sols/er_${tag}_${seed}.edges >/dev/null 2>&1; $S/check.sh $C1/sols/er_${tag}_${seed}.edges >> $C1/deep.tsv 2>&1; fi
  [ "${c:-99}" -gt 4 ] && rm -f $out
done
