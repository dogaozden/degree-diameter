#!/bin/bash
# usage: screen.sh TLIM SEED COMBOFILE   (lines: ORDER ID HT KT)
# runs t26 on c18/groups/sg_ORDER_ID.txt with subs/sub6_ORDER_ID.txt; appends one line per run to run/screen.tsv
D=/home/user/degree-diameter/research/squads/handsoff-65/c26
TL=$1; SD=$2; CF=$3
while read o i ht kt; do
  g=sg_${o}_${i}
  r=$(timeout $((TL+30)) nice -n 10 $D/t26 $D/../c18/groups/$g.txt $D/subs/sub6_${o}_${i}.txt $ht $kt $SD $TL 12 $D/run/scr_${o}_${i}_${ht}${kt}.edges 2>/dev/null | grep RESULT | awk '{print $2}')
  printf '%s\t%s\t%s|%s\t%s\t%s\n' "$o" "$i" "$ht" "$kt" "$SD" "${r:-ERR}" >> $D/run/screen.tsv
done < "$CF"
