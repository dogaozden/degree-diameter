#!/bin/bash
# sweep: group table, alpha index, a ; SECS per run
cd /home/user/degree-diameter/research/squads/d75-r1/c3
export TMPDIR=$PWD/tmp
for spec in "k312sl.ht 0" "k312sl.ht 1" "k304q.ht 0" "k304q.ht 5" "k301.ht 8" "k301.ht 7" "k305.ht 6" "k305.ht 4" "k312q8.ht 0" "k312q8.ht 1" "k327.ht 2" "k312sl.ht 2"; do
  set -- $spec
  for a in 1 2 3; do
    timeout 100 nice -n 10 ./c3s tmp/$1 $a $2 8 7 >> sweep.log 2>&1
  done
done
echo SWEEPDONE >> sweep.log
