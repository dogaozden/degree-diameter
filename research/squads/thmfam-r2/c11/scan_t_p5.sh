#!/bin/bash
# c11: for each m, scan the ratio t = F(-2)/F(2) over all residues t in 1..m-1 (rule pw:1:t), mean excess over the 4 q's
D=/home/user/degree-diameter/research/squads/thmfam-r2/c11
T=/home/user/degree-diameter/research/theorems/haar_families
for m in 7 13 19 31 37 43; do
  for t in $(seq 1 $((m-1)) ); do
    OUT=$(nice -n 10 timeout 900 python3 $T/cover_score.py --p 5 --rule x --qs 13,17,19,23 --ms $m --gen "python3 $D/gen_nl.py {p} {q} {m} pw:1:$t" 2>&1 | grep SUMMARY | python3 -c "import sys,json; s=json.loads(sys.stdin.read()[8:]); print(s['mean_excess'], s['n_full'])" 2>/dev/null)
    echo "m=$m t=$t mean_excess n_full: $OUT"
  done
done
