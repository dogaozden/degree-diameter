#!/bin/bash
# exhp_list.sh LIST OUTLOG : exhaustive Delta=5 Haar search (haar5 exhp, S ∋ e, all 4-subsets) for each "N I" line of LIST
T=$(dirname $0); mkdir -p $T/../tables/exhp
while read n i; do
  [ -z "$i" ] && continue
  f=$T/../tables/exhp/g${n}_$i.bin
  [ -f $f ] || python3 $T/gapgroup.py table $n $i $f
  r=$(timeout 1800 $T/haar5 exhp $f 5 0 | tail -1)
  echo "$n $i :: $r" >> $2
  rm -f $f
done < $1
echo DONE >> $2
