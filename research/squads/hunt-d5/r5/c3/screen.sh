#!/bin/bash
# screen.sh FROM TO : seed screen of specs.txt lines FROM..TO (3 seeds x 8 s, K=16, COOL=10, REHEAT=40)
cd /home/user/degree-diameter/research/squads/hunt-d5/r5/c3
from=$1; to=$2
n=0
while read N p k r m; do
  n=$((n+1)); [ $n -lt $from ] && continue; [ $n -gt $to ] && break
  dir=runs/N${N}_m${m}_p${p}_k${k}_r${r}
  mkdir -p $dir
  COOL=10 REHEAT=40 timeout 60 nice -n 10 ../../tools/farm.sh $dir 9 8 16 1 3 meta $p $k $r $m
  echo "spec $N meta $p $k $r $m : $(grep -o 'best=[0-9]*' $dir/farm.log | tr '\n' ' ')"
done < specs.txt
