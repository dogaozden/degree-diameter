#!/bin/bash
# SA over bi-coset |H|=|K|=2 graphs for every even-order SmallGroup of orders 722..766 (tasks2.txt, random order)
cd /home/user/degree-diameter/research/squads/handsoff-65/c4
until grep -q DONE3 results.txt 2>/dev/null; do sleep 10; done
while read n i; do
  ./sweep.sh sa 2 6 6 $n $i
done < tasks2.txt
echo DONE2 >> results.txt
