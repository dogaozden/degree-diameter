#!/bin/bash
# 6+6 joint annealing (salift_s, D=10) over every group of order 81 (n = 972), 3 in parallel, 60 s each.
cd /home/user/degree-diameter/research/squads/own-small/runs/p6
for id in 12 9 2 10 11 7 8 3 5 1 4 6 13 14 15; do
  while [ $(jobs -r | wc -l) -ge 3 ]; do sleep 1; done
  D=10 ../../tools/bin/salift_s 6 g81.txt $id 1 60 10 0.3 s81_${id}_1.sol > s81_${id}_1.log 2>&1 &
done
wait; echo DONE > done
