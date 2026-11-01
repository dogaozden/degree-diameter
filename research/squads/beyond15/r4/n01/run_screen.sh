#!/bin/bash
# n01 screen: Tutte/Foster-shape quotient, ANNEAL=10 per (n, lambda), maxlam 3, sequential (one heavy process)
export THREADS=1
Q="3 3 0-0,0-2,0-2,1-0,1-1,1-1,2-0,2-1,2-2"
Q=/home/user/degree-diameter/research/frontier/beyond15/lsym/quotgen.py
cd /home/user/degree-diameter/research/frontier/beyond15/lsym
ANNEAL=10 python3 $Q 16 20467 21600 7 7 "3 3 0-0,0-2,0-2,1-0,1-1,1-1,2-0,2-1,2-2" 2 11 3
ANNEAL=10 python3 $Q 16 20467 21600 9 9 "3 3 0-0,0-2,0-2,1-0,1-1,1-1,2-0,2-1,2-2" 1 12 3
ANNEAL=10 python3 $Q 16 20467 21600 10 10 "3 3 0-0,0-2,0-2,1-0,1-1,1-1,2-0,2-1,2-2" 1 13 3
echo ALLDONE
