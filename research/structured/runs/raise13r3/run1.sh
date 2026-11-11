#!/bin/bash
# usage: run1.sh TAG SECS SEED AR GROUP...   (prod X X n); ORBIT 6 2 1, swap-conjugation order 6
TAG=$1; SECS=$2; SEED=$3; AR=$4; shift 4
cd /home/user/degree-diameter/research/theorems/order2
OUT=/home/user/degree-diameter/research/structured/runs/raise13r3/$TAG.sol.txt
ORBIT="6 2 1" ASWAPC=1 AR=$AR THREADS=1 BESTOUT=/home/user/degree-diameter/research/structured/runs/raise13r3/$TAG.best.txt \
  nice -n 5 timeout $((SECS+300)) ./haar_order2 13 8 $SECS $SEED 8 $OUT "$@" > /home/user/degree-diameter/research/structured/runs/raise13r3/$TAG.log 2>&1
echo "EXIT $?" >> /home/user/degree-diameter/research/structured/runs/raise13r3/$TAG.log
