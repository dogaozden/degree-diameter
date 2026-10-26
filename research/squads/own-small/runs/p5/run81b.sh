#!/bin/bash
cd /home/user/degree-diameter/research/squads/own-small/runs/p5
for id in $(seq 4 15); do
  while [ $(jobs -r | wc -l) -ge 3 ]; do sleep 1; done
  D=10 ../../tools/bin/salift_s 5 g81.txt $id 1 45 10 0.3 s81_${id}_1.sol > s81_${id}_1.log 2>&1 &
done
wait; echo DONE81 > done81
