#!/bin/bash
# run2.sh: remaining groups (lines 5-13 of groups.txt), 6 seeds x 6 s each
cd /home/user/degree-diameter/research/squads/hunt-d5/r5/b7
sed -n "5,13p" groups.txt | while read N p k r n; do
  dir=g${N}_p${p}_k${k}_r${r}_n${n}
  rm -rf $dir; mkdir -p $dir
  COOL=10 REHEAT=40 timeout 400 nice -n 10 ../../tools/farm.sh $PWD/$dir 7 6 16 1 6 meta $p $k $r $n
done
echo ALLDONE
