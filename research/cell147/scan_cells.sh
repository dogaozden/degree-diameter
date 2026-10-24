#!/bin/bash
# Random-matching misses per source for extra-copy lifts GH(q)+j over Z_m, D=7, one line per configuration.
# cell q j m target(vertices to beat)
while read cell q j m target; do
  [ -z "$cell" ] && continue
  ht=$(python3 htpick.py $m $j | awk '{for(i=1;i<='$j';i++) printf "%s ", $i}')
  case $q in 2|3) S=0;; 5) S=200;; 7) S=40;; 11) S=8;; 13) S=4;; esac
  out=$(GROUP="cyc $m" HT="$ht" EVAL=1 SAMPLE=$S ./glift data/gh_$q.txt $j 7 0 7 /dev/null 2>&1 | tr '\n' ' ')
  P=$(head -1 data/gh_$q.txt | cut -d' ' -f1)
  tot=$(echo "$out" | sed -n 's/.*total misses \([0-9]*\).*/\1/p')
  ns=$S; [ "$S" = 0 ] && ns=$((2*P))
  verts=$((2*P*m))
  echo "$cell q=$q j=$j m=$m HT=[$ht] vertices=$verts (to beat $target) misses/source=$(echo "scale=2; $tot/$ns" | bc)"
done
