#!/bin/bash
# usage: run_dir.sh CHUNKTAG  -- anneals every d/*.dc2, appends to results.txt, keeps best<=40
cd /home/user/degree-diameter/research/squads/s65r6/c3
TOOLS=/home/user/degree-diameter/research/s65/tools
for f in d/*.dc2; do
  [ -f "$f" ] || continue
  b=${f%.dc2}
  out=$(SA=1 SECS=2 SEED=1 timeout 60 nice -n 10 $TOOLS/dcenum "$f" 6 5 "$b.edges" 2>&1)
  best=$(echo "$out" | sed -n 's/.*best \([0-9-]*\) vertices.*/\1/p' | tail -1)
  [ -z "$best" ] && best=NA
  echo "$(basename $f) $best" >> results.txt
  if [ "$best" = "0" ]; then
    echo "RECORD CANDIDATE $f" >> CANDIDATES.txt
    nice -n 10 $TOOLS/score65 "$b.edges" >> CANDIDATES.txt 2>&1
    nice -n 10 $TOOLS/apsp "$b.edges" 6 5 >> CANDIDATES.txt 2>&1
  fi
  if [ "$best" != "NA" ] && [ "$best" -le 40 ]; then
    mv "$f" keep/; [ -f "$b.edges" ] && mv "$b.edges" keep/
  else
    rm -f "$f" "$b.edges"
  fi
done
echo "$(date +%H:%M:%S) chunk $1 done" >> progress.txt
