#!/bin/bash
# anneal every exported pair: SA=1 SECS=3 SEED=1, 60 s timeout; results to results.txt; delete cost > 40
cd /home/user/degree-diameter/research/squads/s65r5/c8
DC=/home/user/degree-diameter/research/s65/tools/dcenum
for f in d/*.dc2; do
  [ -e "$f" ] || continue
  b=$(basename "$f" .dc2)
  if grep -q "^$b " results.txt 2>/dev/null; then continue; fi
  line=$(SA=1 SECS=3 SEED=1 timeout 60 nice -n 10 $DC "$f" 6 5 "e/$b.edges" 2>/dev/null | grep '^RESULT' | tail -1)
  best=$(echo "$line" | sed -n 's/.* best \([0-9-]*\) .*/\1/p')
  if [ -z "$best" ]; then echo "$b NOANSWER" >> results.txt; rm -f "$f"; continue; fi
  echo "$b cost $best" >> results.txt
  if [ "$best" -gt 40 ]; then rm -f "$f" "e/$b.edges"; fi
  if [ "$best" -le 1 ]; then echo "CANDIDATE $b cost $best" >> candidates.txt; fi
done
echo ANNEALDONE >> results.txt
