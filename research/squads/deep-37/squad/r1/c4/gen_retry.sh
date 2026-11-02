#!/bin/bash
# gen_retry.sh : re-generate the few-orbit G-sets for groups whose first attempt hit the GAP time limit (MAXR 6, CAP 30)
cd /home/user/degree-diameter/research/squads/deep-37
for spec in "24 14" "24 15" "36 10" "36 12" "36 13" "36 14"; do
  set -- $spec
  rm -rf squad/r1/c4/gs/n170/g$1_$2
  timeout 260 bash squad/r1/c4/run_few_long.sh $1 $2 170 6 30
  echo "g$1_$2 done"
done
echo RETRY_DONE
