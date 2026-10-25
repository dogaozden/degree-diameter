#!/bin/bash
# usage: run_batch.sh M tmax seed...   (one process at a time; A uses the duality pair, B/C use matching seed = anneal seed)
cd /home/user/degree-diameter/research/squads/r3-d8/c6
M=$1; TMAX=$2; shift 2
for s in "$@"; do
  for v in A B C; do
    if [ "$v" = A ]; then MF=work/hopsA.txt; else MF=work/hops${v}_s${s}.txt; fi
    OUT=runs/${v}_M${M}_s${s}.txt
    timeout 900 nice -n 10 ./lanneal_c6 work/h3.txt "$MF" "$M" "$TMAX" "$s" 2 64 "$OUT" 2>runs/${v}_M${M}_s${s}.err | tail -1 | sed "s/^/variant $v /" >> runs/results.txt
    echo "  liftdiam $v M$M s$s: $(timeout 300 nice -n 10 /home/user/degree-diameter/research/theorems/d8/liftdiam "$OUT" 8 1 | tail -1)" >> runs/results.txt
  done
done
