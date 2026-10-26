#!/bin/bash
cd /home/user/degree-diameter/research/squads/own-small/runs/d11
for s in 2 3 4 5 6 7; do
  while [ $(jobs -r | wc -l) -ge 2 ]; do sleep 1; done
  if [ $s -le 3 ]; then
    START=s81_p8_5.sol.best D=11 ../../tools/bin/salift_s2 8 g81.txt 5 $s 150 3 0.3 push5_$s.sol > push5_$s.log 2>&1 &
  else
    D=11 ../../tools/bin/salift_s2 8 g81.txt 5 $s 150 10 0.3 push5_$s.sol > push5_$s.log 2>&1 &
  fi
done
wait; echo DONE > push5.done
