#!/bin/bash
# seeds $1..$2 of the full line scan (overlap order) at q = 11
for s in $(seq $1 $2); do
  timeout 600 python3 ext_all.py 11 ../../../d10D7/sets/P11_r6c7_756.txt ../../../d10D7/sets/L11_spread.txt allscan/q11_s$s $s ovl 300 500 2>&1 | grep RESULT
done
