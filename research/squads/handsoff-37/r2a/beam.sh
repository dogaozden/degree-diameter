#!/bin/bash
# Beam of exhaustive pair insertions (k=2, pair + ab edge): usage beam.sh START.edges LEVELS KEEP
# Level L: insert into every beam graph of level L-1, keep the KEEP best (by far) as L<L>_<j>.edges.
cd /home/user/degree-diameter/research/squads/handsoff-37/r2a
START=$1; LEVELS=$2; KEEP=$3; tag=$(basename "$START" .edges)
D=out/beam/$tag; mkdir -p $D; rm -f $D/*
cp "$START" $D/L0_1.edges
for L in $(seq 1 $LEVELS); do
  rm -f $D/cand_*
  i=0
  for f in $D/L$((L-1))_*.edges; do
    i=$((i+1)); timeout 300 nice -n 10 ./insert "$f" 2 0 $KEEP $D/cand_${i} > /dev/null 2>&1
  done
  ls $D/cand_*_far*.edges | sed -E 's/.*_far([0-9]+)\.edges$/\1 &/' | sort -n | head -$KEEP | awk '{print $2}' > $D/sel_L$L.txt
  j=0; while read f; do j=$((j+1)); cp "$f" $D/L${L}_$j.edges; done < $D/sel_L$L.txt
  echo "level $L: $(head -1 $D/L${L}_1.edges) vertices, beam fars: $(for f in $D/L${L}_*.edges; do ./score37 $f | grep -o 'far=[0-9]*'; done | tr '\n' ' ')"
done
