#!/bin/bash
# usage: run_full.sh  -> exhaustive tlift over all groups of the window; jobs run 4 at a time
cd "$(dirname "$0")"
jobs=()
for n in $(seq 145 180); do jobs+=("k2_3.txt $n"); done
for n in $(seq 73 90); do jobs+=("b4_0.txt $n"); done
for b in b6_0 b6_1 b6_2; do for n in $(seq 49 60); do jobs+=("$b.txt $n"); done; done
printf '%s\n' "${jobs[@]}" | xargs -P 4 -I{} bash -c 'set -- {}; b=$1; n=$2; tag=$(basename $b .txt); timeout 7200 nice ./tlift groups/g$n.txt bases/$b 8 sols 0 1 > runs/full/${tag}_n$n.log 2>&1' 
echo ALLDONE
