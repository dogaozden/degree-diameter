#!/bin/bash
# harvest.sh: copy every solution whose independent check log says VALID into research/frontier/sols/ (stem.txt)
cd "$(dirname "$0")"
for f in runs/*.out; do stem=$(basename $f .out)
  if grep -qh "^VALID" runs/$stem.gen.txt runs/$stem.metacheck.txt 2>/dev/null; then
    [ -f ../sols/$stem.txt ] || { cp $f ../sols/$stem.txt; echo "harvested $stem"; }
  fi
done
