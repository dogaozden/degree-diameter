#!/bin/bash
# gen_all.sh : generate few-orbit G-sets + PROBE estimates for the c4 groups (run in background, log to gen.log)
cd /home/user/degree-diameter/research/squads/deep-37
for spec in "18 3 10 60" "18 4 10 60" "24 3 8 60" "24 12 6 60" "24 13 6 60" "36 11 6 60" "36 9 7 60" "48 48 5 60"; do
  set -- $spec
  s=$(date +%s)
  timeout 900 bash squad/r1/c4/run_few.sh $1 $2 170 $3 $4
  echo "elapsed $(( $(date +%s) - s ))s"
done
echo ALLGEN_DONE
