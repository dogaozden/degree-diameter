#!/bin/bash
# Full scoring (qrange 23..113, psl, m=1) of the screened best 3 per Delta, plus random baselines (3 seeds each).
FS=/home/user/degree-diameter/research/theorems/haar_families/family_score.py
G=/home/user/degree-diameter/research/squads/thmfam-r1/c11/gen_c11.py
R=/home/user/degree-diameter/research/theorems/haar_families/gen_random_orb.py
cd /home/user/degree-diameter/research/theorems/haar_families
for spec in "6 1" "6 7" "6 11" "8 3" "8 7" "8 6"; do
  set -- $spec
  echo "== c11 D=$1 V=$2"
  nice -n 10 timeout 900 python3 $FS --gen "python3 $G {q} {m} $2 $1" --group psl --qrange 23 113 | tail -1
done
for s in 1 2 3; do
  echo "== random D=6 seed=$s"
  nice -n 10 timeout 900 python3 $FS --gen "python3 $R {q} 0 2 $s" --group psl --qrange 23 113 | tail -1
done
for s in 1 2 3; do
  echo "== random D=8 seed=$s"
  nice -n 10 timeout 900 python3 $FS --gen "python3 $R {q} 2 2 $s" --group psl --qrange 23 113 | tail -1
done
echo DONE
