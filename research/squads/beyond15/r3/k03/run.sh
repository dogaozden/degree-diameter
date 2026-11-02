#!/bin/bash
# k03: quotient of Tutte-8-cage/Foster, Z_k covers for k = 6..14, windows just above the records.
Q="3 3 0-0,0-2,0-2,1-0,1-1,1-1,2-0,2-1,2-2"
cd /home/user/degree-diameter/research/frontier/beyond15/lsym
for D in 15 16; do
  if [ $D = 15 ]; then V0=11791; else V0=20467; fi
  for k in 6 7 8 9 10 11 12 13 14; do
    M=$((6*k)); L=$(( (V0 + M - 1) / M * M )); V1=$((L + M*3))
    echo "=== D=$D k=$k window $L..$V1"
    ANNEAL=5 python3 quotgen.py $D $L $V1 $k $k "$Q" 2 1 2
  done
done
echo ALLDONE
