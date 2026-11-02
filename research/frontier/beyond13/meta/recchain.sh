#!/bin/bash
# recchain.sh d D m k r START LINKS SEED0: chained hmeta links (T0 8, T1 1, REHEAT 400) from a saved S
cd "$(dirname "$0")"; d=$1; D=$2; m=$3; k=$4; r=$5; S=$6; links=$7; s0=$8
for i in $(seq 1 $links); do out=rec/c_d${d}D${D}_${m}_${k}_$i
  res=$(START=$S T0=8 T1=1 REHEAT=400 THREADS=1 timeout 100 ./hmeta $d $D 90 $((s0 + i)) 8 $out $m $k $r 2>/dev/null | grep RESULT); echo "$out $res"
  case "$res" in *best=0\ *) echo FOUND $out; exit 0;; esac; [ -f $out.best ] && S=$out.best; done
