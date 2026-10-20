#!/bin/sh
# regularize each big hexagon doubling, then check it with bigcheck (4 threads)
B=/Users/dogaozden/AI_Projects/research-lab/verify/bigcheck/bigcheck
H=../hats/runs
for spec in "q9 11 hex_q9_big" "q11 13 hex_q11_big" "q13 15 hex_q13_big" "q13a3 16 hex_q13_a3_big"; do
  set -- $spec
  echo "=== $1 Delta=$2 ($(date))"
  python3 regularize.py $H/$3.txt $2 graphs/reg_$1_d$2 || continue
  $B -t 4 graphs/reg_$1_d$2.txt $2 6
done
echo "=== done $(date)"
