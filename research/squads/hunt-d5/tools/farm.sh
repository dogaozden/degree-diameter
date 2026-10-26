#!/bin/bash
# farm.sh DIR d SECONDS K SEED0 NSEEDS meta m k r n  (env COOL REHEAT passed through): haar_fast seeds, near misses kept
dir=$1; d=$2; sec=$3; K=$4; s0=$5; ns=$6; shift 6
for ((s=s0; s<s0+ns; s++)); do
  r=$(SAVEBEST=1 THREADS=1 timeout $((sec+20)) $(dirname $0)/haar_fast $d 5 $sec $s $K $dir/s$s.sol "$@" | grep -E "RESULT|wrote" | tr '\n' ' ')
  echo "seed=$s $r" >> $dir/farm.log
done
echo DONE >> $dir/farm.log
