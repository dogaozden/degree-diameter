#!/bin/sh
# summary.sh: best 5 per scan tsv in runs/
cd /home/user/degree-diameter/research/squads/handsoff-65/c9/runs || exit 1
for f in *.tsv; do
  n=$(wc -l < "$f"); echo "$f ($n groups): $(grep -v ERR "$f" | sort -t"$(printf '\t')" -k4 -n | head -5 | awk -F'\t' '{printf "[o%s g%s %s c=%s] ", $1,$2,$3,$4}')"
done
