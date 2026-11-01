#!/bin/bash
# lmulti.sh BASE D n SECS SEED0 NSEEDS: many short lift anneals (cyclic lifts, lift.c of squad r2/e16); stops at the first cost 0
cd "$(dirname "$0")"; B=$1; D=$2; n=$3; sec=$4; s0=$5; ns=$6
for s in $(seq $s0 $((s0 + ns - 1))); do tag=d3D${D}_$(basename $B .txt)_n${n}_s$s
  r=$(timeout $((sec + 10)) ../bin/lift $B $n $D $sec $s out/$tag 2.0 0.05 20000 2>&1 | grep RESULT); echo "$tag $r"
  case "$r" in *best=0\ *) echo FOUND $tag; exit 0;; esac; done
