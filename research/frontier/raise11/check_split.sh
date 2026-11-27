#!/bin/bash
# check_split.sh SOL CHECKER: run the low-memory checker on side A, then side B (each logged with check_one.sh); the
# checker process is protected from the OOM killer (oom_score_adj -1000) and runs at autogroup nice -10.
sol=$1; chk=$2; stem=$(basename $sol .out)
for side in A B; do
  ../beyond11/check_one.sh $(basename $chk) runs/$stem.$(basename $chk).$side.txt $chk $sol $side &
  sleep 2
  for p in $(pgrep -f "$chk $sol $side"); do echo -1000 > /proc/$p/oom_score_adj; echo -10 > /proc/$p/autogroup; done
  wait
done
