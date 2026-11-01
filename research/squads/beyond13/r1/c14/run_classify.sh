#!/bin/bash
C=/home/user/degree-diameter/research/squads/beyond13/r1/c14
cd $C
for g in "sl 61 7" "sl 113 1" "sl 37 31" "sl 53 13" "sl 29 97" "psl 151 1" "psl 79 7" "psl 47 31" "psl 31 97" "psl 67 13"; do
  echo "=== $g"; nice -n 10 python3 classify.py $g
  echo "--- low-cost samples (cost<=40)"; CMAX=40 nice -n 10 python3 classify.py $g
done > classify_all.txt 2>&1
echo done > CLASSIFY_DONE
