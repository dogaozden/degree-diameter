#!/bin/bash
T=/home/user/degree-diameter/research/squads/b48/tools
D=/home/user/degree-diameter/research/squads/b48/r1/c29
THREADS=1 timeout 120 nice -n 10 python3 $T/groups.py "psl2 7 x dih 7" $D/g_PSL27xD7.bin > $D/build2_PSL27xD7.log 2>&1
THREADS=1 timeout 120 nice -n 10 $T/lift $T/bases/bouquet_4semi.txt $D/g_PSL27xD7.bin 4 8 60 77 8 $D/best_PSL27xD7 QUIET=1 2>&1 | grep RESULT | sed 's/^/PSL27xD7_s77 /'
for spec in "A5xD19|perm 5 1,2,0,3,4 ; 1,0,3,2,4 x dih 19" "A5xD20|perm 5 1,2,0,3,4 ; 1,0,3,2,4 x dih 20"; do
  tag=${spec%%|*}; s=${spec#*|}
  THREADS=1 timeout 120 nice -n 10 python3 $T/groups.py "$s" $D/g_$tag.bin > $D/build2_$tag.log 2>&1
  THREADS=1 timeout 120 nice -n 10 $T/lift $T/bases/bouquet_4semi.txt $D/g_$tag.bin 4 8 25 5 8 $D/sol_$tag QUIET=1 2>&1 | grep RESULT | sed "s/^/$tag /"
  rm -f $D/g_$tag.bin
done
echo ALLDONE
