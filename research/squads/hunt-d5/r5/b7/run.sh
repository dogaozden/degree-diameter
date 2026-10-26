#!/bin/bash
# run.sh LINE_START LINE_END : farm 6 seeds x 6 s per group from groups.txt
cd /home/user/degree-diameter/research/squads/hunt-d5/r5/b7
sed -n "$1,$2p" groups.txt | while read N p k r n; do
  dir=g${N}_p${p}_k${k}_r${r}_n${n}
  mkdir -p $dir
  COOL=10 REHEAT=40 timeout 400 nice -n 10 ../../tools/farm.sh $PWD/$dir 7 6 16 1 6 meta $p $k $r $n
done
