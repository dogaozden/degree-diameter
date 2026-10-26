#!/bin/bash
# screen.sh SECS: short flift anneals (d=3, D=9) for every job line; results appended to screen.tsv
E=/home/user/degree-diameter/research/squads/own-small/r1/e2
S=${1:-2}
while read name b N gid path; do
  r=$(/home/user/degree-diameter/research/squads/own-small/tools/bin/flift $E/bases/$name.txt $path 3 9 $S 1 2>/dev/null | grep RESULT)
  best=$(echo "$r" | sed -E 's/.*best=([0-9]+).*/\1/')
  printf "%s\t%d\t%d\t%d\t%s\n" "$name" "$b" "$N" "$gid" "$best" >> $E/runs/screen.tsv
done < $E/work/jobs.txt
echo DONE >> $E/runs/screen.tsv
