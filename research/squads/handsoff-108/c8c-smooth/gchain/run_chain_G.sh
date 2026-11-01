#!/bin/bash
# G and u of the chain-minimum states of the A/B arms (secs = 0: evaluation only), using haar_smooth's SMSTAT line
cd /home/user/degree-diameter/research/squads/handsoff-108/c8c-smooth/gchain
for arm in base s1 s2; do
  log=../ab_$arm.log; [ -f $log ] || continue
  i=0
  grep '^CHAIN' $log | awk '{print $4, $0}' | while read -r mn rest; do
    i=$((i+1))
    S=$(echo "$rest" | awk '{for(k=NF-9;k<=NF;k++) printf "%s ", $k}')
    printf 'CKPT d=10 evals=0 elapsed=0 best=0\n%s\n' "$S" > ${arm}_$i.ckpt
    out=$(ORBIT="3 3 1" ORBW=3 SMSTAT=1 THREADS=1 CKPT=${arm}_$i.ckpt timeout 300 nice -n 10 ../haar_smooth 10 8 0 108961 8 /dev/null psl 23 97 2>&1 | grep "SMSTAT start")
    echo "$arm chain_min=$mn $out"
  done
done
