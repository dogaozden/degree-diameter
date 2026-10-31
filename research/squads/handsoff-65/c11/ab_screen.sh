#!/bin/bash
# usage: ab_screen.sh SECS ORDER ID "a:0:0 ..." : swap symmetry with f = identity (abelian groups only), appends ab_screen.tsv
C=/home/user/degree-diameter/research/squads/handsoff-65/c11
SECS=$1; o=$2; id=$3; shift 3
G=$C/tabs/sg_${o}_${id}.txt
for spec in $@; do
  IFS=: read a p q <<< "$spec"
  B=$C/bases/sym_a${a}_${p}${q}.base; S=$C/bases/sym_a${a}_${p}${q}.sym
  [ -f $B ] || python3 $C/mksym.py $a $p $q $B $S >/dev/null 2>&1 || continue
  r=$(FMAP=$C/tabs/id$o.txt INIT=random SECS=$SECS SEED=$((o*31+id*7+a*3+p*2+q)) timeout 100 nice -n 10 $C/tsym $B $S $G $C/abl_${o}_${id}_a${a}.sol 2>/dev/null | grep RESULT)
  c=$(echo "$r" | awk '{print $3}')
  printf '%s\t%s\t%s\ta%s\t%s\n' "$o" "$id" "$(cut -d' ' -f1 $C/tabs/sg_${o}_${id}.name)" "a${a}p${p}q${q}" "${c:-NA}" >> $C/ab_screen.tsv
done
