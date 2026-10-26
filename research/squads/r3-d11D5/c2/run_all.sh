#!/bin/bash
# sequential runs of wpo from the four cost-2 starts; stops at the first cost-0 state
cd /home/user/degree-diameter/research/squads/r3-d11D5/c2
P=/home/user/degree-diameter/research/d11D5/plus
i=0
for name in y901 f5 g61 u602; do
  i=$((i+1))
  timeout 900 nice -n 10 env THREADS=1 SECS=440 SEED=$i OUT=out_$name.in OUT0=fail0_$name.in ./wpo $P/best_$name.in > log_$name.txt 2>&1
  if grep -q FAIL0 log_$name.txt; then echo "FAIL0 in $name" ; break; fi
done
echo ALLDONE
