#!/bin/bash
cd /home/user/degree-diameter/research/squads/beyond15/r1/a03/chain
F=/home/user/degree-diameter/research/frontier
T=/home/user/degree-diameter/research/squads/beyond15/r1/a03/tutte8.txt
env THREADS=1 timeout 100 nice -n 10 $F/bin/lift $T 300 15 80 21 t300 2.0 0.05 1200 > t300.log 2>&1
echo "tutte8 n=300 lift: $(grep RESULT t300.log)" >> summary2.txt
if [ -f t300.edges ]; then echo "FOUND t300.edges" >> summary2.txt; fi
env START=t300.best THREADS=1 timeout 100 nice -n 10 $F/bin/scan $T 300 15 80 22 t300s 6 > t300s.log 2>&1
echo "tutte8 n=300 scan: $(grep -i RESULT t300s.log)" >> summary2.txt
if [ -f t300s.edges ]; then echo "FOUND t300s.edges" >> summary2.txt; fi
echo DONE >> summary2.txt
