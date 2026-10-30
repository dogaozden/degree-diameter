#!/bin/bash
# c2 driver: sequential coset sweeps (one heavy process at a time), stops launching new orders after DEADLINE (epoch secs)
C=/home/user/degree-diameter/research/beyond-haar-d5/coset
P=/home/user/degree-diameter/research/squads/bh5-r3/c2/progress.txt
DEADLINE=$1; shift
cd $C
for spec in "$@"; do
  set -- $spec
  now=$(date +%s)
  if [ $now -ge $DEADLINE ]; then echo "STOP deadline before $1 $2 $(date +%T)" >> $P; break; fi
  echo "START $1 $2 $(date +%T)" >> $P
  timeout 240 nice -n 10 ./sweep.sh $1 $2 5
  echo "END $1 $2 rc=$? $(date +%T)" >> $P
  rm -rf tmp_$1_$2
done
echo ALLDONE $(date +%T) >> $P
