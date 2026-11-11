#!/bin/bash
# usage: batch.sh SEED LISTFILE  (each line: N m k r; 20 s per run; RESULT lines appended to runs/log.txt)
H=/home/user/degree-diameter/research/frontier/beyond14/bin/hmeta
D=/home/user/degree-diameter/research/squads/beyond14/r4/f08
S=$1; L=$2
cd "$D"
while read N m k r; do
  timeout 105 nice -n 10 env THREADS=1 T0=8 T1=1 REHEAT=400 $H 4 14 20 $S 16 runs/m${m}_k${k}_s${S}.sol $m $k $r 2>/dev/null | grep RESULT | sed "s/^/s=$S file=m${m}_k${k}_s${S} /" >> runs/log.txt
done < "$L"
