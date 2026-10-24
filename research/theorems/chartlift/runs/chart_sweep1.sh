#!/bin/bash
# R2 = universal + pencil (WS=1 WP=1 WD=0): what is the fewest singular patterns per (k,q)?
cd "$(dirname "$0")/.."
for kq in "3 2" "3 3" "3 4" "3 5" "4 2" "4 3" "4 4" "5 2" "5 3"; do
  set -- $kq; k=$1; q=$2
  timeout 200 ./chart_anneal tables/gf$q.txt $k 90 $((k*100+q)) 1 1 0 charts/r2_k${k}_q${q}.txt | tail -1 | sed "s/^/R2 k=$k q=$q: /"
done
