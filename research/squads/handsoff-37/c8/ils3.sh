#!/bin/bash
cd /home/user/degree-diameter/research/squads/handsoff-37/c8
for seed in 11 12 13 14 15 16; do
  python3 kick.py best170_far46.edges out/ils3_in.edges 3 $seed
  nice -n 10 ./lns 170 $((700+seed)) 60 3 0.8 0.5 2 out/ils3 out/ils3_in.edges 0.3 2>&1 | grep -E "DONE" | sed "s/^/kick3 seed $seed: /"
done
echo ILS3DONE
