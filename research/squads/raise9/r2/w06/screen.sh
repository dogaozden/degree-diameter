#!/bin/bash
# usage: screen.sh LISTFILE OUTTSV [SAMPLES]; each line: "<haar_gen3 group args incl. trailing n><TAB><label>"
B=/home/user/degree-diameter/research/squads/raise9/bin
LIST=$1; OUT=$2; S=${3:-1000}
while IFS=$'\t' read -r spec label; do
  [ -z "$spec" ] && continue
  line=$(RANDSAMPLE=$S THREADS=1 timeout 60 nice -n 10 $B/haar_gen3 6 9 1 1 8 /dev/null $spec 2>/dev/null | grep RANDSAMPLE)
  echo -e "$spec\t$label\t$line" >> "$OUT"
done < "$LIST"
