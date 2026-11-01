#!/bin/bash
# anneal_multi.sh BASE D SECS "n:l1,l2 n:l1,..." : liftsym anneals (any n), one per (n, lambda), log to stdout
cd "$(dirname "$0")/.."; B=$1; D=$2; S=$3
for nl in $4; do n=${nl%%:*}; for l in $(echo ${nl#*:} | tr ',' ' '); do
  tag=lsym/out/$(basename $B .txt)_D${D}_n${n}_l${l}_a
  r=$(timeout $((S + 15)) ./bin/liftsym lsym/$B lsym/$(basename $B .txt).perm $n $l $D $S 1 $tag 2>/dev/null | grep RESULT)
  echo "$tag $r"; done; done
