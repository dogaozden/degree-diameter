#!/bin/bash
# c11: score the leading rules at p=7 (q in 11,13,17,19) and p=13 (q in 17,19)
D=/home/user/degree-diameter/research/squads/thmfam-r2/c11
T=/home/user/degree-diameter/research/theorems/haar_families
MS=7,13,19,31,37,43
for R in lin sq pw:1:2 pw:2:1 pw:1:-2 pw:1:3 pw:1:0 pw:1:-3; do
  OUT=$(nice -n 10 timeout 900 python3 $T/cover_score.py --p 7 --rule x --qs 11,13,17,19 --ms $MS --gen "python3 $D/gen_nl.py {p} {q} {m} $R" 2>&1 | grep SUMMARY | cut -c9- | python3 -c "import sys,json; s=json.loads(sys.stdin.read()); print(s['mean_excess'], s['n_full'], {k:v['vertices'] for k,v in s['best'].items() if k in ('8','9','10')})" 2>&1 | tail -1)
  echo "p7 $R $OUT"
done
for R in lin sq pw:1:2 pw:2:1 pw:1:-2 pw:1:0 sqa0 mixc ab; do
  OUT=$(nice -n 10 timeout 900 python3 $T/cover_score.py --p 13 --rule x --qs 17,19 --ms $MS --gen "python3 $D/gen_nl.py {p} {q} {m} $R" 2>&1 | grep SUMMARY | cut -c9- | python3 -c "import sys,json; s=json.loads(sys.stdin.read()); print(s['mean_excess'], s['n_full'], {k:v['vertices'] for k,v in s['best'].items() if k in ('8','9','10')})" 2>&1 | tail -1)
  echo "p13 $R $OUT"
done
