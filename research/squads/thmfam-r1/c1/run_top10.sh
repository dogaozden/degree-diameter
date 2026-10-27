#!/bin/bash
# full-score the 10 best screened pairs with family_score.py (psl, q in [23,113])
D=/home/user/degree-diameter/research/squads/thmfam-r1/c1
i=0
while IFS=$'\t' read -r mean h X Y rest; do
  i=$((i+1))
  set -- $X $Y
  GEN="python3 $D/gen_lift.py {q} {m} $1 $2 $3 $4 $5 $6 $7 $8"
  cd /home/user/degree-diameter/research/theorems/haar_families
  nice -n 10 timeout 900 python3 family_score.py --gen "$GEN" --group psl --qrange 23 113 > $D/logs/full_$i.txt 2>&1
  echo "rank $i screen=$mean h=$h X=($X) Y=($Y) :: $(grep SUMMARY $D/logs/full_$i.txt | cut -c1-200)" >> $D/logs/summary.txt
done < $D/top10.tsv
echo DONE >> $D/logs/summary.txt
