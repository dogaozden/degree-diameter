#!/bin/bash
# Full scores (q in [23,113], psl) of the 10 best screened c2 candidates, then the random Delta=7 baseline (5 seeds).
C2=/home/user/degree-diameter/research/squads/thmfam-r1/c2
HF=/home/user/degree-diameter/research/theorems/haar_families
cd $HF
i=0
while IFS=$'\t' read -r mean vals F X Y rest; do
  i=$((i+1))
  nice -n 10 timeout 900 python3 family_score.py --gen "python3 $C2/gen_c2.py {q} {m} $F $X $Y" --group psl --qrange 23 113 > $C2/full_$i.log 2>&1
  echo "cand $i screen=$mean F=$F X=$X Y=$Y" >> $C2/full_index.txt
done < <(head -10 $C2/screen.tsv)
for s in 1 2 3 4 5; do
  nice -n 10 timeout 900 python3 family_score.py --gen "python3 gen_random_orb.py {q} 1 2 $s" --group psl --qrange 23 113 > $C2/rand_seed$s.log 2>&1
  echo "rand seed $s done" >> $C2/full_index.txt
done
echo ALLDONE >> $C2/full_index.txt
