#!/bin/bash
# usage: batch1.sh seed  -> runs all 13 groups once each with the given seed, 20 s each, appends RESULT lines to log
H=/home/user/degree-diameter/research/frontier/beyond14/bin/hmeta
cd /home/user/degree-diameter/research/squads/beyond14/r4/f08
S=$1; shift
while read N m k r; do
  timeout 105 nice -n 10 env THREADS=1 T0=8 T1=1 REHEAT=400 $H 4 14 20 $S 16 runs/m${m}_k${k}_s${S}.sol $m $k $r 2>&1 | grep RESULT | sed "s/^/s=$S file=m${m}_k${k}_s${S} /" >> runs/log.txt
done < "$@"
