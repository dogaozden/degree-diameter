#!/bin/bash
cd /home/user/degree-diameter/research/squads/bh5b-r2/c5
while ! grep -q DONE long176.log 2>/dev/null; do sleep 3; done
for i in 177 178 5; do
  for b in b22_33 b22_24; do
    out=$(D=5 SECS=10 SEED=1 OUT=sols/s192_${b}_${i}.txt timeout 100 nice -n 10 ./vl bases/$b.txt grp192/sg_192_$i.txt 2>/dev/null | grep RESULT)
    echo "192_$i $b $out" >> screen192.log
  done
done
echo DONE >> screen192.log
