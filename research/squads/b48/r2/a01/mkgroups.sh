#!/bin/bash
T=/home/user/degree-diameter/research/squads/b48/tools
cd /home/user/degree-diameter/research/squads/b48/r2/a01
for e1 in 1 3; do for e2 in 1 2 3 4 5 6; do
  timeout 120 nice -n 10 python3 $T/abc.py build "28 5:4@$e1,2:7@$e2" g/v_${e1}_${e2}.bin || echo FAIL $e1 $e2
done; done
ls -la g
