#!/bin/bash
# k = 8 bases (4+4 cubic bipartite multigraphs), all groups of orders 37..46, first free voltage over Aut-orbit reps.
cd "$(dirname "$0")"
jobs=()
for n in $(seq 37 46); do for b in 0 1 2 3 4 5 6 7; do jobs+=("$b $n"); done; done
printf '%s\n' "${jobs[@]}" | xargs -P ${PAR:-3} -I{} bash -c 'set -- {}; b=$1; n=$2; timeout 14400 nice ./tlift3 groups/g$n.txt bases/b8_$b.txt 8 sols 0 1 -1 groups/reps_$n.txt > runs/k8/b8_${b}_n$n.log 2>&1'
echo ALLDONE
