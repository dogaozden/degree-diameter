#!/bin/bash
# usage: run_pat.sh FIRST LAST SEED  (patterns.txt lines FIRST..LAST, 15 CPU-s each, cycles of 3 CPU-s)
cd /home/user/degree-diameter/research/squads/hunt-d5/r4/w1
T=../../tables/mt_53_26_16.bin
sed -n "$1,$2p" patterns.txt | nl -v$1 -ba | while read n c pt f; do
  j=$(echo "$pt" | tr ',' '\n' | awk 'BEGIN{z=0} {if($1==0 && z==0){z=1; next} print $1}' | paste -sd' ')
  timeout 150 nice -n 10 ./pfill $T 9 1 15 $3 3 pat $j > logs/pat_${n}_$3.log 2>&1
  echo "pat$n cost0=$c pattern=$pt $(grep -o 'best=[0-9]*' logs/pat_${n}_$3.log) $(grep -o 'cycles=[0-9]*' logs/pat_${n}_$3.log) $(grep -o 'evals=[0-9]*' logs/pat_${n}_$3.log)"
done
