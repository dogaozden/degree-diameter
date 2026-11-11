#!/bin/bash
# usage: scan.sh d D seconds listfile tag  (one hmeta run per group; log to scan_<tag>.log)
B=/home/user/degree-diameter/research/frontier/beyond13
cd /home/user/degree-diameter/research/squads/beyond13/r3/f15
d=$1; D=$2; S=$3; L=$4; T=$5
while read m k r N mu; do
  out=sol_${T}_${m}_${k}_${r}
  res=$(THREADS=1 nice -n 10 timeout 200 $B/meta/hmeta $d $D $S 7 8 $out $m $k $r 2>&1 | grep RESULT)
  echo "$m $k $r N=$N mu=$mu :: $res" >> scan_${T}.log
done < $L
echo DONE >> scan_${T}.log
