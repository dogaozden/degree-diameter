#!/bin/bash
# squad c2: flags for every chart written by the anneal runs (singular count, pencil fails, diagonal flags)
C=/home/user/degree-diameter/research/squads/r2-chartlift/c2
cd /home/user/degree-diameter/research/theorems/chartlift || exit 1
for f in "$@"; do
  echo "$(basename $f): $(grep FINAL ${f%.txt}.log 2>/dev/null | cut -c1-110) | $(timeout 300 nice -n 10 python3 chartflags.py $f 3 5 $C/tmpcheck.flags)"
done
rm -f $C/tmpcheck.flags
