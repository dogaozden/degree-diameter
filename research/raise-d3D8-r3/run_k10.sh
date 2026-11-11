#!/bin/bash
# Round 3: k = 10 bases (5+5 cubic bipartite multigraphs, 15 classes from enum3.py), all groups of order N,
# first free voltage over Aut(G)-orbit representatives. Usage: run_k10.sh "29 31 33" 
cd "$(dirname "$0")"
mkdir -p runs/k10 sols/k10
jobs=()
for n in $1; do for b in $(seq 0 14); do jobs+=("$b $n"); done; done
printf '%s\n' "${jobs[@]}" | xargs -P ${PAR:-4} -I{} bash -c 'set -- {}; b=$1; n=$2; timeout 14400 nice ./tlift groups/g$n.txt bases/b10/b10_$b.txt 8 sols/k10 0 1 $n groups/reps_$n.txt > runs/k10/b10_${b}_n$n.log 2>&1'
echo ALLDONE
