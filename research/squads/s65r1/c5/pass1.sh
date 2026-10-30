#!/bin/bash
cd /home/user/degree-diameter/research/squads/s65r1/c5
for spec in "690 8" "692 5" "694 2" "698 2" "696 44" "700 36" "702 62"; do
  set -- $spec
  ./sweep_diag.sh $1 2 6 4 "[1..$2]"
  echo "done $1 $(date +%T)" >> logs/pass1_progress.txt
done
echo ALLDONE >> logs/pass1_progress.txt
