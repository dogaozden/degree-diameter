#!/bin/bash
# exhaustive |H|=|K|=3 over all SmallGroups of orders 1083..1149 divisible by 3 that the library has (orders3.txt)
cd /home/user/degree-diameter/research/squads/handsoff-65/c4
while read n c; do
  ids=$(seq 1 $c | tr '\n' ' ')
  ./sweep.sh ex 3 6 0 $n $ids
done < orders3.txt
echo DONE3 >> results.txt
