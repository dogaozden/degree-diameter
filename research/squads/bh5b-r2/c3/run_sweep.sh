#!/bin/bash
# sweep the orders downward (card c3) until the deadline passes (checked between orders)
cd /home/user/degree-diameter/research/squads/bh5b-r2/c3
deadline=$1; shift
for o in "$@"; do
  now=$(date +%s); [ $now -ge $deadline ] && { echo "STOP before $o at $(date)"; break; }
  echo "START $o $(date)"
  timeout 900 nice -n 10 ./sweep.sh $o 2 7 20 "[1..NrSmallGroups($o)]" 1
  echo "DONE $o $(date)"
done
echo ALLDONE $(date)
