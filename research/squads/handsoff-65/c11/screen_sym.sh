#!/bin/bash
# usage: screen_sym.sh SECS ORDER ID "a:p:q ..."   runs tsym on symmetric bases; appends to sym_screen.tsv
C=/home/user/degree-diameter/research/squads/handsoff-65/c11
SECS=$1; o=$2; id=$3; shift 3
G=$C/tabs/sg_${o}_${id}.txt
for spec in $@; do
  IFS=: read a p q <<< "$spec"
  B=$C/bases/sym_a${a}_${p}${q}.base; S=$C/bases/sym_a${a}_${p}${q}.sym
  [ -f $B ] || python3 $C/mksym.py $a $p $q $B $S >/dev/null 2>&1 || continue
  r=$(INIT=random SECS=$SECS SEED=$((o*31+id*7+a*3+p*2+q)) timeout 100 nice -n 10 $C/tsym $B $S $G 2>/dev/null | grep RESULT)
  c=$(echo "$r" | awk '{print $3}')
  printf '%s\t%s\t%s\t%s\t%s\n' "$o" "$id" "$(cut -d' ' -f1-3 $C/tabs/sg_${o}_${id}.name | tr ' ' '_')" "a${a}p${p}q${q}" "${c:-NA}" >> $C/sym_screen.tsv
done
