#!/bin/bash
cd /home/user/degree-diameter/research/squads/s65r4/c5
T=/home/user/degree-diameter/research/s65/tools
for k in 1 4 6 9 11; do
  SECS=90 SEED=1 timeout 200 nice -n 10 $T/tabu a${k}n.base N53.txt a${k}_s1.sol > a${k}_s1.out 2> a${k}_s1.err
  echo "a$k s1: $(grep RESULT a${k}_s1.out) | last best: $(grep '^best' a${k}_s1.err | tail -1)"
done
