#!/bin/bash
# usage: screen.sh listfile samples outfile ; each line: N m k r ...
B=/home/user/degree-diameter/research/squads/raise9/bin
S=$2
while read N m k r rest; do
  line=$(RANDSAMPLE=$S THREADS=1 timeout 60 nice -n 10 $B/haar_gen3 6 9 100 1 8 /dev/null meta $m $k $r 1 2>/dev/null | grep RANDSAMPLE)
  echo "meta $m $k $r N=$N :: $line" >> $3
done < $1
