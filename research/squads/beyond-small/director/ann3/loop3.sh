#!/bin/bash
cd "$(dirname "$0")"
for i in $(seq 1 12); do
  T0=0.6; T1=0.05
  ./anneal3 ../../data/d16D5_n33792.edges pool0.txt pool1.txt init83.txt 280 $((i*13+5)) $T0 $T1 1.5 state.txt valid_best.txt > chunk_$i.log 2>&1
  echo "$i $(wc -l < valid_best.txt 2>/dev/null)" >> loop3.log
done
