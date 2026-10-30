#!/bin/bash
# one-screen status of the running searches
cd "$(dirname "$0")"
date -u +%H:%M
echo "HITS:"; cat exh/runs/HITS.txt 2>/dev/null
for p in b4a2y b4a1x haar5x; do
  for f in $(ls exh/runs/${p}_[0-9]*.txt 2>/dev/null | sort -t_ -k2 -n); do
    o=$(basename $f .txt | sed "s/${p}_//"); n=$(wc -l < $f); s=$(awk -F'solutions ' '{split($2,a," "); s+=a[1]} END{print s+0}' $f)
    printf "%s %s: %s groups, %s solutions; " $p $o $n $s
  done; echo
done
echo "(7,5) best by file:"; for f in coset/logs/sw_*.txt; do b=$(awk '{for(i=1;i<=NF;i++) if($i=="best"){print $(i+1); break}}' $f | sort -n | head -1); echo -n "$(basename $f .txt) $b ($(wc -l < $f)); "; done; echo
ls coset/logs/HIT_* 2>/dev/null
