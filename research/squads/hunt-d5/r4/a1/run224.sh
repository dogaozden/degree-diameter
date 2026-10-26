#!/bin/bash
# run224.sh START_EPOCH WALL_DEADLINE_S : exhp d=5 over order224.txt groups, appends to results224.txt
cd "$(dirname "$0")"
T=../../tools
start=$1; lim=$2
while read i gd; do
  now=$(date +%s); el=$((now-start))
  [ $el -ge $lim ] && break
  f=g224_$i.bin
  timeout 120 nice -n 10 python3 $T/gapgroup.py table 224 $i $f || { echo "224 $i :: TABLE FAIL" >> results224.txt; continue; }
  r=$(OMP_NUM_THREADS=1 THREADS=1 timeout 120 nice -n 10 $T/haar5 exhp $f 5 0 | grep -E "^(RESULT|cost 0)" | tr '\n' ' ')
  echo "224 $i Gp=$gd :: $r" >> results224.txt
  rm -f $f
done < order224.txt
echo "STOP at $(date +%s) elapsed $(( $(date +%s)-start ))" >> results224.txt
