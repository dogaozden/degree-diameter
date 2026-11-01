#!/bin/bash
# n02: quotient "3 3 0-0,0-2,0-2,1-0,1-1,1-1,2-0,2-1,2-2" (Tutte/Foster shape), D=16, k=11..16, ANNEAL screen
cd /home/user/degree-diameter/research/frontier/beyond15/lsym
Q="3 3 0-0,0-2,0-2,1-0,1-1,1-1,2-0,2-1,2-2"
for k in 11 12 13 14 15 16; do
  THREADS=1 ANNEAL=4 python3 quotgen.py 16 20467 21600 $k $k "$Q" 2 1 3 > /home/user/degree-diameter/research/squads/beyond15/r4/n02/run_k$k.log 2>&1
done
echo ALLDONE > /home/user/degree-diameter/research/squads/beyond15/r4/n02/done.flag
