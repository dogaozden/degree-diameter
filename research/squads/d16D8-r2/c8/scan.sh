#!/bin/bash
# usage: scan.sh BASE OUTLIST : list the sources (base vertices) with uncovered pairs, via 50-source blocks then single sources
B=/home/user/degree-diameter/research/d16D8/baselift
BASE=$1; OUT=$2; V=$(head -1 "$BASE" | cut -d' ' -f1)
: > "$OUT"
for ((s=0; s<V; s+=50)); do
  e=$((s+49)); [ $e -ge $V ] && e=$((V-1))
  seq $s $e > "$OUT.blk"
  u=$(SRCFILE="$OUT.blk" THREADS=1 $B eval "$BASE" 6 | sed -n 's/.*uncovered=\([0-9]*\).*/\1/p')
  if [ "$u" != "0" ]; then
    for ((x=s; x<=e; x++)); do
      echo $x > "$OUT.one"
      v=$(SRCFILE="$OUT.one" THREADS=1 $B eval "$BASE" 6 | sed -n 's/.*uncovered=\([0-9]*\).*/\1/p')
      [ "$v" != "0" ] && echo $x >> "$OUT"
    done
  fi
done
rm -f "$OUT.blk" "$OUT.one"
echo "failing sources: $(wc -l < "$OUT")"
