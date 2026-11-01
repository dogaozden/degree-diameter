#!/bin/bash
cd /home/user/degree-diameter/research/squads/beyond15/r1/a03/chain
F=/home/user/degree-diameter/research/frontier
T=/home/user/degree-diameter/research/squads/beyond15/r1/a03/tutte8.txt
for n in 330 340; do
  env THREADS=1 timeout 100 nice -n 10 $F/bin/lift $T $n 15 50 31 t$n 2.0 0.05 1200 > t$n.log 2>&1
  echo "tutte8 n=$n lift: $(grep RESULT t$n.log)" >> summary3.txt
  if [ ! -f t$n.edges ]; then
    env START=t$n.best THREADS=1 timeout 100 nice -n 10 $F/bin/scan $T $n 15 45 32 t${n}s 6 > t${n}s.log 2>&1
    echo "tutte8 n=$n scan: $(grep -i RESULT t${n}s.log)" >> summary3.txt
  fi
  if [ -f t$n.edges ]; then echo "FOUND n=$n t$n.edges" >> summary3.txt
  elif [ -f t${n}s.edges ]; then echo "FOUND n=$n t${n}s.edges" >> summary3.txt; fi
done
echo DONE >> summary3.txt
