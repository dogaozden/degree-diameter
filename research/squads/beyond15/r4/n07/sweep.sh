#!/bin/bash
# n07: K3,3 quotient, exhaustive symmetric lifts, D=15, prime n, k=3..6 (one log per k)
F=/home/user/degree-diameter/research/frontier
export THREADS=1
Q="3 3 0-0,0-1,0-2,1-0,1-1,1-2,2-0,2-1,2-2"
cd $F/beyond15/lsym
for k in 3 4 5 6; do
  python3 $F/beyond15/lsym/quotgen.py 15 11803 12700 $k $k "$Q" 6 1 4 > /home/user/degree-diameter/research/squads/beyond15/r4/n07/k$k.log 2>&1
done
echo ALLDONE >> /home/user/degree-diameter/research/squads/beyond15/r4/n07/k6.log
