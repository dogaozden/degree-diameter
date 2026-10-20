#!/bin/sh
# second independent check (hats/tools/check_big, needs "n m" header) of the regular graphs
until grep -q "=== done" run_big.log; do sleep 20; done
for f in reg_q5_d7_n9348 reg_q9_d11 reg_q11_d13; do
  n=$(head -1 graphs/$f.txt); m=$(( $(wc -l < graphs/$f.txt) - 1 ))
  { echo "$n $m"; tail -n +2 graphs/$f.txt; } > /private/tmp/claude-501/-Users-dogaozden-AI-Projects-degree-diameter/d6bfe58f-ec9f-4fe8-a39d-9588c6bb9afc/scratchpad/$f.nm.txt
  echo "== $f"; ../hats/tools/check_big /private/tmp/claude-501/-Users-dogaozden-AI-Projects-degree-diameter/d6bfe58f-ec9f-4fe8-a39d-9588c6bb9afc/scratchpad/$f.nm.txt 6
  rm /private/tmp/claude-501/-Users-dogaozden-AI-Projects-degree-diameter/d6bfe58f-ec9f-4fe8-a39d-9588c6bb9afc/scratchpad/$f.nm.txt
done
