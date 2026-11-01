#!/bin/bash
# n04 driver: Gray-shape quotient, k = 10..20, ANNEAL=10, one pattern and one lambda per (k, n) (time box)
Q="3 3 0-0,0-2,0-2,1-0,1-0,1-1,2-1,2-1,2-2"
cd /home/user/degree-diameter/research/frontier/beyond15/lsym
for k in 10 11 12 13 14 15 16 17 18 20; do
  echo "=== k=$k start $(date +%T)"
  ANNEAL=10 THREADS=1 python3 quotgen.py 16 20467 21800 $k $k "$Q" 1 3 1
  echo "=== k=$k end $(date +%T)"
done
