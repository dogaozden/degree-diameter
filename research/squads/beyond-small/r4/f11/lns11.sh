#!/bin/bash
# lns11.sh ITERS NS CLQ : exact-repair loop for side B (card f11). Drops R=4..6 orbits, rebuilds clique on the
# pool of covers compatible with the kept orbits (rep.c), keeps the result if it has at least as many orbits.
cd "$(dirname "$0")"
IT=$1; NS=$2; CLQ=$3
for i in $(seq 1 $IT); do
  R=$((4 + RANDOM % 3))
  shuf cur.txt | head -n -$R > fix_k.txt
  nice -n 10 ./rep ../../data/d16D5_n33792.edges fix_k.txt try_k.txt 0 $RANDOM 6 4000 $NS $CLQ > rep_k.log 2>&1
  a=$(wc -l < cur.txt); b=$(wc -l < try_k.txt 2>/dev/null || echo 0)
  if [ "$b" -ge "$a" ]; then cp try_k.txt cur.txt; fi
  echo "$i drop $R: $a -> $b (cur $(wc -l < cur.txt)) $(grep -o 'exact [01]\|TIMED OUT' rep_k.log | head -1)" >> lns11.log
done
