#!/bin/bash
# usage: screen.sh BASEIDS SECS SEED  -> one vl run per (base, group of order 60); appends to screen.txt
for b in $1; do for g in $(seq 1 13); do
  r=$(cd .. && D=5 SECS=$2 SEED=$3 OUT=b6/sol_b${b}_g${g}_s$3.sol nice -n 5 ./vl b6/b33_$b.txt groups/sg_60_$g.txt 2>/dev/null | grep RESULT)
  echo "b$b g$g s$3 $r" >> screen.txt
done; done
