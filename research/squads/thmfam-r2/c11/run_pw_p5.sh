#!/bin/bash
D=/home/user/degree-diameter/research/squads/thmfam-r2/c11
T=/home/user/degree-diameter/research/theorems/haar_families
for AB in "1:-1" "1:1" "1:0" "0:1" "1:2" "1:-2" "1:3" "1:-3" "2:1" "3:1" "1:-4" "2:-1" "3:-1" "3:2" "2:3" "1:4"; do
  R=pw:${AB%%:*}:${AB##*:}
  OUT=$(nice -n 10 timeout 900 python3 $T/cover_score.py --p 5 --rule x --qs 13,17,19,23 --ms 7,13,19,31,37,43 --gen "python3 $D/gen_nl.py {p} {q} {m} $R" 2>&1 | grep SUMMARY | python3 -c "import sys,json; s=json.loads(sys.stdin.read()[8:]); print(s['mean_excess'], s['n_full'], {k:v['vertices'] for k,v in s['best'].items() if k in ('8','9','10')})" 2>/dev/null)
  echo "$R mean_excess,n_full,best_V: $OUT"
done
