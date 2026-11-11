#!/bin/bash
# n03 chain: Gray-shape quotient, ANNEAL screen, k = 11..16 (THREADS=1)
export THREADS=1 ANNEAL=10
cd /home/user/degree-diameter/research/frontier/beyond15/lsym
Q="3 3 0-0,0-2,0-2,1-0,1-0,1-1,2-1,2-1,2-2"
echo "START $(date +%T)"
timeout 300 python3 quotgen.py 15 11803 12900 11 11 "$Q" 3 11 3
echo "DONE k11 $(date +%T)"
timeout 330 python3 quotgen.py 15 11803 12900 13 13 "$Q" 3 13 3
echo "DONE k13 $(date +%T)"
timeout 300 python3 quotgen.py 15 11803 12900 12 12 "$Q" 2 12 1
echo "DONE k12 $(date +%T)"
timeout 300 python3 quotgen.py 15 11803 12900 14 14 "$Q" 2 14 1
echo "DONE k14 $(date +%T)"
timeout 240 python3 quotgen.py 15 11803 12900 15 15 "$Q" 2 15 1
echo "DONE k15 $(date +%T)"
timeout 280 python3 quotgen.py 15 11803 12900 16 16 "$Q" 2 16 1
echo "DONE k16 $(date +%T)"
