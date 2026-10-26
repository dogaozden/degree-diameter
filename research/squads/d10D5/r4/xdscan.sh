#!/bin/bash
# xdscan.sh STATE C0 "FDSET" "x:L x:L ...": initial (coset-0, holes) for each candidate ordinary flag deletion
X=$1; C=$2; FS=$3; HA="$(python3 hubadj.py $X "$FS")"; FR="$(awk '$1=="free"{$1="";print}' $X)"
for t in $4; do
  r=$(FREE="$FR" FDSET="$FS" XDEL="$t" GEN=1 RELAX=2 PENW=2 HUBADJ="$HA" BASE=gq/gq_q7.bin NPOLY=4 SEED=1 IN=$C OUT=/dev/null PTARG=0 SWAPP=0 ITERS=1 TEMP0=0.1 TEMP1=0.02 nice -n 5 ./dmgen 7 2>&1 | awk '/initial cost/ {c=$11} /penalty/ {h=$5} END {print c, h}' | tr -d ',')
  echo "$t $r"
done
