#!/bin/bash
# n05: composite-n symmetric lifts over the Tutte/Foster-shape quotient (3,15), k = 5..14
F=/home/user/degree-diameter/research/frontier
cd $F/beyond15/lsym
for k in 5 6 7 8 9 10 11 12 13 14; do
  echo "=== k=$k $(date +%T)"
  THREADS=1 ANNEAL=3 timeout 900 python3 quotgen.py 15 11803 12700 $k $k "3 3 0-0,0-2,0-2,1-0,1-1,1-1,2-0,2-1,2-2" 2 3 1
done
echo ALLDONE $(date +%T)
