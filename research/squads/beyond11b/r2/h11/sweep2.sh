#!/bin/bash
cd /home/user/degree-diameter/research/squads/beyond11b/r2/h11
CAND=$1; D=$2; LOG=$3; touch $LOG; start=$(date +%s)
while read N spec; do
  s=$(echo "$spec" | tr '_' ' ')
  grep -qF "$s |" $LOG 2>/dev/null && continue
  now=$(date +%s); if [ $((now-start)) -gt 85 ]; then break; fi
  timeout 60 nice -n 10 python3 run1.py "$s" "p$(echo $spec | tr -c 'a-z0-9' '_')_D$D" $D >> $LOG 2>&1
done < $CAND
