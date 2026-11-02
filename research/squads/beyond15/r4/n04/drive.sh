#!/bin/bash
# n04 driver: Gray-shape quotient, k = 10..20, ANNEAL=10 per (n, lambda), exact-order lambda, 1 pattern, 1 lambda (time box)
Q="3 3 0-0,0-2,0-2,1-0,1-0,1-1,2-1,2-1,2-2"
cd /home/user/degree-diameter/research/squads/beyond15/r4/n04
for k in 10 11 12 13 14 15 16 17 18 20; do
  echo "=== k=$k start $(date +%T)"
  ANNEAL=10 THREADS=1 python3 quotgen_ord.py 16 20467 21800 $k $k "$Q" 1 3 1
  echo "=== k=$k end $(date +%T)"
done
