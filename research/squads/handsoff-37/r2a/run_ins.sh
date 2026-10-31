#!/bin/bash
# usage: run_ins.sh K FILE...   exhaustive insertion (k=2: pair+ab edge, k=3: three edges) into each 168 seed
cd /home/user/degree-diameter/research/squads/handsoff-37/r2a
K=$1; shift
for f in "$@"; do
  b=$(basename $f .edges)
  out=out/ins/${b}_k${K}
  timeout 500 nice -n 10 ./insert $f $K 0 10 $out 2> logs/ins_${b}_k${K}.err | head -3 | tr '\n' ' ' | sed "s|^|$b k$K: |"; echo
done
