#!/bin/bash
cd /home/user/degree-diameter/research/squads/handsoff-65/c2
for k in $(seq 0 17); do
  SECS=60 SEED=1 INIT=random nice -n 10 timeout 200 ../shared/tabu bases/class3_$k.base groups/sg_116_2.txt long/class3_$k.edges 2>/dev/null | grep RESULT | sed "s/^/class $k /" >> classes.txt
done
echo CLASSDONE
