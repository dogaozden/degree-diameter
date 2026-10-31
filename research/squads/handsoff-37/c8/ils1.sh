#!/bin/bash
cd /home/user/degree-diameter/research/squads/handsoff-37/c8
BEST=best170_far46.edges
for seed in 1 2 3 4; do
  python3 kick.py $BEST out/ils_in.edges 1 $seed
  echo "== kick seed $seed k=1 start far $(../bin/score37 out/ils_in.edges | sed 's/.*far=\([0-9]*\).*/\1/')"
  nice -n 10 ./lns 170 $((100+seed)) 40 3 0.6 0.5 2 out/ils out/ils_in.edges - 2>/dev/null
done
echo ALLDONE
