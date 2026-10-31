#!/bin/bash
# greedy growth: GH(2,2) -> n = 170: exhaustive best 2-edge insertion (insbest), then LNS repair 15 s (T 0.8, s 3)
cd /home/user/degree-diameter/research/squads/handsoff-37/c8
cur=out/gh126.edges
for k in $(seq 1 22); do
  ./insbest $cur out/gi_in.edges 2>> out/ggrow.log > /dev/null
  n=$((126 + 2*k))
  nice -n 10 ./lns $n $((400+k)) 15 3 0.8 0.5 2 out/gg out/gi_in.edges 2>/dev/null > /dev/null
  cp out/gg_best.edges out/ggcur_$k.edges
  cur=out/ggcur_$k.edges
  echo "n=$n lns_far=$(../bin/score37 $cur | sed 's/.*far=\([0-9]*\).*/\1/')"
done
echo GGDONE
