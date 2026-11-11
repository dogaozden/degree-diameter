#!/bin/bash
# lsweep.sh D TARGET_VERTICES SECONDS: cyclic-lift sweep over the cubic bases (lift.c from squad r2/e16)
cd "$(dirname "$0")"; D=$1; T=$2; sec=${3:-40}
for b in bases/*.txt; do nb=$(head -1 $b); n=$(( (T + nb - 1) / nb )); tag=d3D${D}_$(basename $b .txt)_n$n
  r=$(timeout $((sec + 10)) ../bin/lift $b $n $D $sec 7 out/$tag 2.0 0.05 20000 2>&1 | grep RESULT); echo "$tag $r"; done
