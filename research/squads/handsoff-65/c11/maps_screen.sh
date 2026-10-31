#!/bin/bash
# usage: maps_screen.sh ORDER ID SECS K1 K2 "a:p:q ..."  : swap symmetry with f = inv o theta for theta = invs/f_ORDER_ID_k
C=/home/user/degree-diameter/research/squads/handsoff-65/c11
o=$1; id=$2; SECS=$3; k1=$4; k2=$5; shift 5
G=$C/tabs/sg_${o}_${id}.txt
for k in $(seq $k1 $k2); do
  for spec in $@; do
    IFS=: read a p q <<< "$spec"
    B=$C/bases/sym_a${a}_${p}${q}.base; S=$C/bases/sym_a${a}_${p}${q}.sym
    [ -f $B ] || python3 $C/mksym.py $a $p $q $B $S >/dev/null 2>&1 || continue
    r=$(FMAP=$C/invs/f_${o}_${id}_${k}.map INIT=random SECS=$SECS SEED=$((k*13+a*3+p*2+q)) timeout 100 nice -n 10 $C/tsym $B $S $G $C/maps/m_${o}_${id}_${k}_a${a}${p}${q}.sol 2>/dev/null | grep RESULT)
    c=$(echo "$r" | awk '{print $3}')
    fx=$(awk 'NR==1{a=$0} {print}' $C/invs/f_${o}_${id}_${k}.map | tr ' ' '\n' | awk '{i=NR-1; if ($1==i) n++} END{print n+0}')
    printf '%s\t%s\tk%s\tfix%s\ta%s%s%s\t%s\n' "$o" "$id" "$k" "$fx" "$a" "$p" "$q" "${c:-NA}" >> $C/maps_screen.tsv
  done
done
