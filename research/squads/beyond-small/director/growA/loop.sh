#!/bin/bash
cd "$(dirname "$0")"
cp fixedA32_swap.txt cur.txt
for i in $(seq 1 25); do
  ./growb ../ann/Gswap.edges cur.txt out_$i.txt 90 $((i+100)) 6 4000 > run_$i.log 2>&1
  if [ -s out_$i.txt ] && [ $(wc -l < out_$i.txt) -ge $(wc -l < cur.txt) ]; then cp out_$i.txt cur.txt; fi
  echo "$i $(wc -l < cur.txt)" >> loop.log
done
