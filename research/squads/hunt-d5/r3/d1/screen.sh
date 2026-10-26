#!/bin/bash
# usage: screen.sh FROM TO SEEDS...   (line numbers in specs.txt)
cd /home/user/degree-diameter/research/squads/hunt-d5/r3/d1
from=$1; to=$2; shift 2
i=0
while read -r m p k r n; do
  i=$((i+1))
  if [ $i -lt $from ] || [ $i -gt $to ]; then continue; fi
  for s in "$@"; do
    line=$(THREADS=1 OMP_NUM_THREADS=1 timeout 40 nice -n 10 ../../tools/haar_fast 6 5 10 $s 16 sol_${p}_${k}_${r}_${n}_s${s}.bin meta $p $k $r $n 2>&1 | grep '^RESULT')
    echo "$i meta $p $k $r $n seed=$s $line" >> screen.log
  done
done < specs.txt
