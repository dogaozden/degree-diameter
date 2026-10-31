#!/bin/bash
# usage: cls_screen.sh ORDER SECS ID1 ID2 ... : for each group, the swap family with f = inv o theta, theta one per
# Aut-conjugacy class of involutions (invs2/), option a2 all-pairs (2:2:2). Appends cls_screen.tsv.
C=/home/user/degree-diameter/research/squads/handsoff-65/c11
o=$1; SECS=$2; shift 2
for id in "$@"; do
  G=$C/tabs/sg_${o}_${id}.txt
  [ -f $C/invs2/c_${o}_${id}.sum ] || (cd $C && timeout 200 nice -n 10 gap -q -c "ORDER:=$o; ID:=$id; OUTDIR:=\"invs2\";" invs2.g >/dev/null 2>&1)
  [ -f $C/invs2/c_${o}_${id}.sum ] || continue
  nm=$(cut -d' ' -f1 $C/tabs/sg_${o}_${id}.name)
  for mp in $C/invs2/c_${o}_${id}_*.map; do
    k=$(basename $mp .map | awk -F_ '{print $4}')
    fx=$(tr ' ' '\n' < $mp | awk '{i=NR-1; if ($1==i) n++} END{print n+0}')
    B=$C/bases/sym_a2_22.base; S=$C/bases/sym_a2_22.sym
    r=$(FMAP=$mp INIT=random SECS=$SECS SEED=$((id*17+k)) timeout 100 nice -n 10 $C/tsym $B $S $G $C/cls/c_${o}_${id}_${k}.sol 2>/dev/null | grep RESULT)
    c=$(echo "$r" | awk '{print $3}')
    printf '%s\t%s\t%s\tk%s\tfix%s\t%s\n' "$o" "$id" "$nm" "$k" "$fx" "${c:-NA}" >> $C/cls_screen.tsv
  done
done
