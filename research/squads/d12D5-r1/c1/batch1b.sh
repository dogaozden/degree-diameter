#!/bin/bash
# batch 1b (replaces the remainder of batch1.sh): cyclic Z_24 for the remaining bases, 25 s CPU, seed 1
C1=/home/user/degree-diameter/research/squads/d12D5-r1/c1
B=/home/user/degree-diameter/research/d12D5
while kill -0 12204 2>/dev/null; do sleep 3; done
R(){ $C1/run.sh "$1" "$2" 25 1; }
for k in 001 002 003 004; do R $B/bases3/k3_$k.txt g24_cyc; done
echo BATCH1_DONE >> $C1/ceiling.txt
