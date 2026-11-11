#!/bin/bash
# usage: screen.sh SAMPLES SEED "fam p n" ... ; runs RANDORB screens, 45 s cap each, prints min cost
B=/home/user/degree-diameter/research/frontier/beyond14/bin/haar_big0
D=/home/user/degree-diameter/research/squads/beyond14/r3/e13
S=$1; SEED=$2; shift 2
for g in "$@"; do
  set -- $g; f=$1; p=$2; n=$3
  out=$D/screen/s_${f}_${p}_${n}.sol
  res=$(RANDORB=$S ORBIT="3 2 0" timeout 45 nice -n 10 env THREADS=1 $B 6 14 90 $SEED 1 $out $f $p $n 2>$D/screen/log_${f}_${p}_${n}.txt | grep RANDORB | tail -1)
  mins=$(grep -o 'cost [0-9]*' $D/screen/log_${f}_${p}_${n}.txt | awk '{print $2}' | sort -n | head -3 | tr '\n' ' ')
  echo "$f $p $n | samples=$(grep -c 'RANDORB sample' $D/screen/log_${f}_${p}_${n}.txt) mins: $mins | ${res:+done}"
done
