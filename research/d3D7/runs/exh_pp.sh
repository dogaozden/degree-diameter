#!/bin/bash
# every lift of every p+p cubic base (bases/p<p>/) over every group of order lo..hi, D = 7, Aut-reduced
# usage: runs/exh_pp.sh p lo hi
cd "$(dirname "$0")/.."
p=$1; lo=$2; hi=$3; out=runs/exh_p${p}_${lo}_${hi}.out
: > $out
for N in $(seq $lo $hi); do for b in bases/p$p/*.txt; do echo "BASE $b" >> $out; AUT=groups/a$N.txt ./bin/liftx $b groups/g$N.txt 7 >> $out; done; done
echo DONE >> $out
