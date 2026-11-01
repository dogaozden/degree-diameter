#!/bin/bash
# usage: sweep.sh CANDFILE D LOG  -- processes lines not yet in LOG, stops after ~90 s
cd /home/user/degree-diameter/research/squads/beyond11b/r2/h11
CAND=$1; D=$2; LOG=$3; touch $LOG
start=$(date +%s)
while read N p k r; do
  tag="m${p}_${k}_${r}_D${D}"
  grep -q "^meta $p $k $r |" $LOG 2>/dev/null && continue
  now=$(date +%s); if [ $((now-start)) -gt 85 ]; then break; fi
  timeout 60 nice -n 10 python3 run1.py "meta $p $k $r" $tag $D >> $LOG 2>&1
done < $CAND
echo "remaining: $(while read N p k r; do grep -q "^meta $p $k $r |" $LOG || echo x; done < $CAND | wc -l)"
