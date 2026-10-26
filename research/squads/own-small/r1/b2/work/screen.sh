#!/bin/bash
# usage: screen.sh LIST SECS OUTFILE  (runs flift on each line "base.txt group.bin N b")
T=/home/user/degree-diameter/research/squads/own-small/tools
R=/home/user/degree-diameter/research/squads/own-small/r1/b2
S=$2
while read base grp N b; do
  res=$($T/bin/flift $R/bases/$base $R/groups/bin/$grp 3 10 $S 7 8 2>/dev/null | grep RESULT)
  best=$(echo "$res" | sed -n 's/.*best=\([0-9]*\).*/\1/p')
  echo "$best $base $grp N=$N b=$b" >> $3
done < $1
