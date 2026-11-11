#!/bin/bash
# harvest.sh: copy every haarcheck_gen-VALID find to research/frontier/sols/ and its check log to
# research/frontier/runs/cloudcheck/<stem>.gen.txt (job beyond-d13)
cd "$(dirname "$0")"
for f in sols/*.txt; do s=$(basename $f .txt)
  [ -f runs/$s.gen.txt ] && grep -q "^VALID" runs/$s.gen.txt || continue
  cp -n $f ../sols/$s.txt; cp runs/$s.gen.txt ../runs/cloudcheck/$s.gen.txt; echo "harvested $s"; done
