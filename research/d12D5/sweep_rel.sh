#!/bin/bash
# usage: sweep_rel.sh BASE TABLE PREFIX SECS SEED OUTLOG   -- runs all 24 relabellings PREFIX_qXX.txt, 4 at a time
B=$1; T=$2; P=$3; S=$4; SEED=$5; L=$6; : > $L
for q in $(seq -w 0 23); do
  echo "$B $T ${P}_q$q.txt $S $SEED q$q"
done | xargs -P 4 -L 1 bash -c 'r=$(timeout $(( $3 + 30 )) nice -n 10 ./mlift_chart $0 $1 $2 $3 $4 2.0 runs/ctrl_$(basename $0 .txt)_$(basename $1 .txt)_$5_s$4.edges | tail -n 1); echo "$5 $r"' >> $L
sort -t= -k5 -n $L | head -n 30 > /dev/null
