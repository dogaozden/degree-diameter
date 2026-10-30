#!/bin/bash
DIR=/home/user/degree-diameter/research/squads/s65r4/c7
cd $DIR
for pair in "176_26 1" "176_26 2" "176_26 3" "176_1 1" "176_7 2" "176_17 1" "176_21 3" "176_10 1" "180_1 1" "180_2 2" "180_14 3" "180_13 1"; do
  set -- $pair
  ./run1.sh $1 $2 60 1
done
echo PASS1_DONE >> $DIR/summary.txt
