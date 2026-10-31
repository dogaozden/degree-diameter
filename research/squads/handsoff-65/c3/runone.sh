#!/bin/bash
# usage: runone.sh LABEL "GAP_GROUP_EXPR" H [MAXSETS]
# exports all bi-coset double-coset files for subgroup classes of order H in G, then dcenum (DELTA 6, D 5)
C3=/home/user/degree-diameter/research/squads/handsoff-65/c3
SH=/home/user/degree-diameter/research/squads/handsoff-65/shared
LABEL=$1; EXPR=$2; H=$3; MS=${4:-3000000}
OUT=$C3/out/${LABEL}_h${H}
timeout 600 nice -n 10 gap -q -c "$PRE GNAME:=\"$LABEL\"; G:=$EXPR; H_ORDER:=$H; OUT:=\"$OUT\";" $SH/dc_export.g > $C3/out/${LABEL}_h${H}.gaplog 2>&1
echo "EXPORT rc=$? $LABEL h=$H"
for f in $OUT*.dc; do
  [ -f "$f" ] || continue
  b=${f%.dc}
  r=$(timeout 600 nice -n 10 $SH/dcenum "$f" 6 5 "$b.edges" $MS 2>$b.err | grep RESULT)
  echo "$(basename $b) :: $r" >> $C3/results.txt
  echo "$(basename $b) :: $r"
done
