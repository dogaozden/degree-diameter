#!/bin/bash
# continue d15's annealing on side A (G) and side B (swapped graph) in 100 s chunks; keep the valid outputs
cd "$(dirname "$0")"
for i in $(seq 1 40); do
  ./anneal ../../data/d16D5_n33792.edges 6 95 $((i*7+1)) 0.2 1.5 stA_in.txt stA_in.txt validA_$i.txt 2>&1 | tail -1 > /dev/null
  ./anneal Gswap.edges 6 95 $((i*7+3)) 0.2 1.5 stB_in.txt stB_in.txt validB_$i.txt 2>&1 | tail -1 > /dev/null
  echo "$i A $(wc -l < validA_$i.txt) B $(wc -l < validB_$i.txt)" >> loop.log
done
