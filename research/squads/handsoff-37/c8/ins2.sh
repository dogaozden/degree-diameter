#!/bin/bash
cd /home/user/degree-diameter/research/squads/handsoff-37/c8
for s in 7 5 3 8; do
  echo "== insertion seed $s"; nice -n 10 ./lns 170 $((500+s)) 240 3 1.0 0.5 2 out/I$s out/ins170_s$s.edges 0.4 2>&1 | grep -E "DONE|best=" | tail -2
done
echo INSDONE
