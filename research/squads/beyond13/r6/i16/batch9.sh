#!/bin/bash
# i16 batch: cyclic lifts of cubic bases with N just above 506 (D = 9)
B=/home/user/degree-diameter/research/frontier/beyond13
L=$B/lifts/bases
O=/home/user/degree-diameter/research/squads/beyond13/r6/i16/out
export THREADS=1
for spec in "gp8_3 32" "gp14_3 19" "gp16_3 16" "gp20_3 13" "heawood 37" "gp10_3 26"; do
  set -- $spec
  echo "== base $1 n $2"
  nice -n 10 $B/bin/lift $L/$1.txt $2 9 60 7 $O/b9_$1_$2 3 0.1 1000 2>&1 | tail -1
  if [ -f $O/b9_$1_$2.edges ]; then echo "COST0 $1 $2"; fi
done
echo ALLDONE
