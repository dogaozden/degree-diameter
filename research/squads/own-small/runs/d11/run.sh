#!/bin/bash
# (3,11) new cell: 8+8 joint annealing (salift_s, D=11) over groups of order 81 (n = 1,296 > 1,250 census graph).
cd /home/user/degree-diameter/research/squads/own-small/runs/d11
for id in 12 9 2 10 11 7 8 3 5 4 6 13 14 15 1; do
  while [ $(jobs -r | wc -l) -ge 2 ]; do sleep 1; done
  D=11 ../../tools/bin/salift_s 8 g81.txt $id 1 60 10 0.3 s81_p8_${id}.sol > s81_p8_${id}.log 2>&1 &
done
wait; echo DONE > done
