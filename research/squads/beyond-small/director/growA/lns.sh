#!/bin/bash
# lns.sh GRAPH BEST TAG ITERS : destroy-and-repair over Z22-orbit packings with growb (r3/e02).
# Each iteration drops R random orbits (R = 2..5), regrows for 60 s, keeps the result if it has at least as many orbits.
cd "$(dirname "$0")"
G=$1; B=$2; T=$3; IT=$4
for i in $(seq 1 $IT); do
  R=$((2 + RANDOM % 4))
  shuf $B | head -n -$R > fix_$T.txt
  ./growb $G fix_$T.txt try_$T.txt 60 $((RANDOM)) 6 4000 > /dev/null 2>&1
  a=$(wc -l < $B); b=$(wc -l < try_$T.txt 2>/dev/null || echo 0)
  if [ "$b" -ge "$a" ]; then cp try_$T.txt $B; fi
  echo "$i drop $R: $a -> $b (best $(wc -l < $B))" >> lns_$T.log
done
