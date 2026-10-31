#!/bin/bash
# conder168 with K random 2-switches, then exhaustive best pair insertion (n = 170), then 30 s LNS (T 0.8 -> 0.3)
cd /home/user/degree-diameter/research/squads/handsoff-37/c8
for seed in 1 2 3 4 5 6 7 8; do
  python3 kick.py ../shared/seeds/conder168.edges out/k168_$seed.edges 2 $seed
  ins=$(./insbest out/k168_$seed.edges out/k170_$seed.edges 2>/dev/null)
  nice -n 10 ./lns 170 $((800+seed)) 30 3 0.8 0.5 2 out/K$seed out/k170_$seed.edges 0.3 2>/dev/null > /dev/null
  echo "seed $seed ins_far=$ins lns_far=$(../bin/score37 out/K${seed}_best.edges | sed 's/.*far=\([0-9]*\).*/\1/')"
done
echo K168DONE
