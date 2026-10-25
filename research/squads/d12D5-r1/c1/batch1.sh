#!/bin/bash
# batch 1: order-24 screen, 25 s CPU, seed 1 (one run at a time)
C1=/home/user/degree-diameter/research/squads/d12D5-r1/c1
B=/home/user/degree-diameter/research/d12D5
K=$B/base_k33m.txt
R(){ $C1/run.sh "$1" "$2" 25 1; }
R $K g24_cyc
R $K g24_z2xz12
R $K g24_SL23
R $K g24_dih12
R $K g24_z2z2z6
for k in 000 001 002 003 004; do
  R $B/bases3/k3_$k.txt g24_cyc
  R $B/bases3/k3_$k.txt g24_z2xz12
done
echo BATCH1_DONE >> $C1/ceiling.txt
