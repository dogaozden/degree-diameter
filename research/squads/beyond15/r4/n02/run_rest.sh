#!/bin/bash
# n02 (restart after load): maxlam 1 for k=12..16 to fit the time box; same quotient, D=16, ANNEAL=4, seed 1
cd /home/user/degree-diameter/research/frontier/beyond15/lsym
Q="3 3 0-0,0-2,0-2,1-0,1-1,1-1,2-0,2-1,2-2"
N=/home/user/degree-diameter/research/squads/beyond15/r4/n02
for k in 12 14 16 13 15; do
  THREADS=1 ANNEAL=4 python3 quotgen.py 16 20467 21600 $k $k "$Q" 2 1 1 > $N/run1_k$k.log 2>&1
done
echo ALLDONE > $N/done.flag
