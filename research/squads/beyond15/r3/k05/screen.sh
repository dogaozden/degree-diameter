#!/bin/bash
# screen.sh LIST D SECS OUT : one short hmeta run per group (d=3, seed 7)
H=/home/user/degree-diameter/research/frontier/bin/hmeta
LIST=$1; DD=$2; SEC=$3; OUT=$4
while read N m k r o f; do
  res=$(env THREADS=1 T0=8 T1=1 REHEAT=400 timeout 60 $H 3 $DD $SEC 7 8 runs/s${DD}_${m}_${k}_${r} $m $k $r | grep RESULT)
  echo "$N $m $k $r ord=$o $res" >> $OUT
done < $LIST
echo DONE >> $OUT
