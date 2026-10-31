#!/bin/bash
# usage: batch.sh  -- exports each SmallGroup(n,id) for the listed orders and runs the (6,5) bi-coset search
W=/home/user/degree-diameter/research/squads/sd5-r1/c7/work
export TMPDIR=/home/user/degree-diameter/research/squads/sd5-r1/c7/tmp
for spec in "1047 2" "1101 2" "1119 2" "1137 2" "1095 2" "1065 2" "1131 2" "1035 2" "1113 2" "1179 2" "1191 2" "1221 2" "1227 2" "1233 2" "1239 2" "1263 2" "1299 2"; do
  set -- $spec; n=$1; k=$2
  for id in $(seq 1 $k); do
    f=$W/SG_${n}_${id}.txt
    timeout 300 nice -n 15 gap -q -c "mygrp:=SmallGroup($n,$id);; OUT:=\"$f\";;" $W/export.g < /dev/null
    timeout 900 nice -n 15 python3 $W/bicoset.py $f 5 6 $W/out2 | tail -1
  done
done
echo BATCHDONE
