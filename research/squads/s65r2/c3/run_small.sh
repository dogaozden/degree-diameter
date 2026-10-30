#!/bin/bash
cd /home/user/degree-diameter/research/squads/s65r2/c3
for spec in "706 [1..2]" "708 [1..10]" "710 [1..6]" "712 [1..15]" "714 [1..12]" "716 [1..4]" "718 [1..2]"; do
  set -- $spec
  echo "START $1 $(date +%T)" >> logs/progress.txt
  timeout 1500 nice -n 10 ./sweep.sh $1 2 6 3 "$2"
  echo "DONE $1 $(date +%T)" >> logs/progress.txt
done
