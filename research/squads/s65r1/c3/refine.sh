#!/bin/bash
# Refine the top 3 screened pairs (lowest cost; ties -> smaller order) with two more seeds at SECS=40.
T=/home/user/degree-diameter/research/s65/tools
G=/home/user/degree-diameter/research/s65/groups/sg
C=/home/user/degree-diameter/research/squads/s65r1/c3
cd $C
OUT=refine.txt
: > $OUT
TOP=$(grep 'cost=' screen.txt | grep -v 'seed=[2-9]' | sed 's/cost=//' | awk '{split($1,a,"_"); print $3, a[2], $1, $2}' | sort -k1,1n -k2,2n | head -3 | awk '{print $3, $4}')
echo "TOP $TOP" >> $OUT
echo "$TOP" | while read gn bn; do
  for seed in 2 3; do
    sol=runs/rf_${gn}_${bn}_s${seed}.sol
    res=$(D=5 SECS=40 ITERS=250000 SEED=$seed OUT=$sol timeout 90 nice -n 10 $T/vl $C/bases/$bn.txt $G/$gn.txt 2>/dev/null | grep '^RESULT best')
    echo "$gn $bn cost=$(echo $res | awk '{print $3}') seed=$seed secs=40 sol=$sol" >> $OUT
  done
done
echo REFINE_DONE >> $OUT
