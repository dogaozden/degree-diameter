#!/bin/bash
# Screen c02 candidates with haar_fast, 1.5 s each, seed 1. Skips (m,k,r) already in the 8 s scan.
cd /home/user/degree-diameter/research/squads/b48/r1/c02
while read N m k r o; do
  if grep -q "^    " ../scan_meta_1092_1120.txt 2>/dev/null; then continue; fi
  out=$(THREADS=1 timeout 120 nice -n 10 /tmp/claude-0/-home-user-degree-diameter/dc6fd85c-f533-550d-af33-040d4dcb67e6/scratchpad/bin/haar_fast 4 8 1.5 1 8 scr_${m}_${k}_${r}.txt meta $m $k $r 1 2>/dev/null | grep RESULT)
  echo "$N $m $k $r $o :: $out"
done < candidates.txt > screen.txt
