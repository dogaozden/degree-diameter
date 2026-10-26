#!/bin/bash
# run_batch.sh LISTFILE DEADLINE_EPOCH : exact haar5 exhp (d=5) over each "N I" in LISTFILE, skipping done ones
T=/home/user/degree-diameter/research/squads/hunt-d5/tools
W=/home/user/degree-diameter/research/squads/hunt-d5/r5/a1
cd $W
while read n i; do
  [ -z "$n" ] && continue
  grep -q "^$n $i " results.txt 2>/dev/null && continue
  [ $(date +%s) -ge $2 ] && { echo "STOP deadline before $n $i" >> progress.log; break; }
  f=$W/g${n}_${i}.bin
  python3 $T/gapgroup.py table $n $i $f >/dev/null 2>&1 || { echo "$n $i tablefail" >> results.txt; continue; }
  r=$(OMP_NUM_THREADS=1 THREADS=1 timeout 300 nice -n 10 $T/haar5 exhp $f 5 0 | tail -1)
  st=$(python3 -c "import sys" ; cat /dev/null)
  echo "$n $i :: $r" >> results.txt
  echo "$(date +%T) done $n $i" >> progress.log
  rm -f $f
done < $1
