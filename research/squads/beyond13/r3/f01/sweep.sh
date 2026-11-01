#!/bin/bash
# usage: sweep.sh LISTFILE SECS SEED ; each line: base_name n
B=/home/user/degree-diameter/research/frontier/beyond13
D=/home/user/degree-diameter/research/squads/beyond13/r3/f01
BASEDIR=${BASEDIR:-$B/lifts/bases}
cd $D
while read base n; do
  out=runs/${base}_${n}_s$3
  THREADS=1 nice -n 10 $B/bin/lift $BASEDIR/$base.txt $n 13 $2 $3 $out >> sweep_log.txt 2>&1
  echo "$base $n $(tail -1 sweep_log.txt)" >> results.txt
done < $1
