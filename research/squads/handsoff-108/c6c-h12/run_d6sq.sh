#!/bin/bash
# c6c-h12: D6 square-reflection family, partition by partition (smallest first), resumable; then a random sample of 6+2+2.
cd /home/user/degree-diameter/research/squads/handsoff-108/c6c-h12
E=./exh12
for spec in "6,3,1" "6,2,1,1" "3,3,3,1" "3,3,2,2" "3,3,2,1,1" "3,2,2,2,1" "2,2,2,2,2" "2,2,2,2,1,1"; do
  nice -n 10 timeout 1500 $E 193 0 85 0 0 1 0 1 2 0 10 scanA $spec out/D6sq_scanA.tsv 2>> out/D6sq_scanA.log
  echo "D6sq $spec rc=$? $(date -u +%H:%M:%S)" >> out/progress.log
done
nice -n 10 timeout 900 $E 193 0 85 0 0 1 0 1 2 0 10 sample 6,2,2 500 108702 > out/D6sq_sample622.out 2>> out/D6sq_sample622.log
echo "D6sq sample 6,2,2 rc=$? $(date -u +%H:%M:%S)" >> out/progress.log
echo "D6sq chain done $(date -u +%H:%M:%S)" >> out/progress.log
