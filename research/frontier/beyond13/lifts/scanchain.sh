#!/bin/bash
# scanchain.sh BASE n D START LINKS: chained runs of scan (squad r5/h02's 1-opt + tabu lift finisher), 95 s each
cd "$(dirname "$0")"; B=$1; n=$2; D=$3; S=$4; links=$5
for k in $(seq 1 $links); do tag=sc_$(basename $B .txt)_D${D}_n${n}_$k
  r=$(START=$S timeout 105 ../bin/scan $B $n $D 95 $((70 + k)) out/$tag 6 2>/dev/null | grep RESULT); echo "$tag $r"
  case "$r" in *best=0\ *) echo FOUND $tag; exit 0;; esac; S=out/$tag.best; done
