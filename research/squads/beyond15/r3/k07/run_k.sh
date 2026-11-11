#!/bin/bash
# run_k.sh D k : quotgen over one k, one random pattern (seed 11), smallest lambda per n, ANNEAL=3 s
cd /home/user/degree-diameter/research/squads/beyond15/r3/k07
D=$1; K=$2
if [ "$D" = "15" ]; then LO=11791; HI=13000; else LO=20467; HI=23000; fi
timeout 100 nice -n 10 env THREADS=1 ANNEAL=3 python3 -u quotgen_k07.py $D $LO $HI $K $K "2 2 0-0,0-0,0-1,1-0,1-1,1-1" 1 11 1 >> sweep_D${D}.log 2>&1
echo "chunk D=$D k=$K exit $?" >> sweep_D${D}.log
