#!/bin/bash
# screen.sh LISTFILE SECS: each line "bin-path"; runs flift on bases b3_0..2 (d=3 D=10), appends RESULT lines.
T=/home/user/degree-diameter/research/squads/own-small/tools
C=/home/user/degree-diameter/research/squads/own-small/r1/c1
SECS=$2
while read g; do
  for b in 0 1 2; do
    r=$(timeout 60 $T/bin/flift $C/bases/b3_$b.txt $g 3 10 $SECS 1 2>/dev/null | grep RESULT)
    echo "$(basename $g) b$b $r" >> $C/scr/screen.tsv
  done
done < $1
