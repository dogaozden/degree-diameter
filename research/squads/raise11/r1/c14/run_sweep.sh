#!/bin/bash
# usage: run_sweep.sh MODE SEED_FROM SEED_TO ORBIT ; appends one line per seed to sweep_<MODE>.tsv
cd /home/user/degree-diameter/research/squads/raise11/r1/c14
for s in $(seq $2 $3); do
  out=$(THREADS=1 FIXMODE=$1 ORBIT="$4" RANDORB=30 timeout 60 nice -n 10 ./haar_c14 7 11 60 $s 4 /dev/null sl 53 37 2>&1)
  sub=$(echo "$out" | grep -o "subgroup [0-9]* of" | awk '{print $2}')
  tries=$(echo "$out" | grep -o "tries [0-9]*" | awk '{print $2}')
  rl=$(echo "$out" | grep "RANDORB d=")
  mn=$(echo "$rl" | grep -o "min=[0-9]*" | cut -d= -f2)
  p10=$(echo "$rl" | grep -o "p10=[0-9]*" | cut -d= -f2)
  med=$(echo "$rl" | grep -o "median=[0-9]*" | cut -d= -f2)
  echo -e "$1\t$s\t$4\t$sub\t$tries\t$mn\t$p10\t$med"
done
