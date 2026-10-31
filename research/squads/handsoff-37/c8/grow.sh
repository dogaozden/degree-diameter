#!/bin/bash
# grow GH(2,2) (126) by one vertex pair per step, LNS repair (15 s, T 0.8) after each insertion, up to n = 170
cd /home/user/degree-diameter/research/squads/handsoff-37/c8
cur=out/gh126.edges
for k in $(seq 1 22); do
  python3 mkins.py $cur out/g_in.edges $((k*7+3)) > /dev/null
  n=$((126 + 2*k))
  nice -n 10 ./lns $n $((300+k)) 15 3 0.8 0.5 2 out/g out/g_in.edges 2>/dev/null > /dev/null
  cp out/g_best.edges out/gcur_$k.edges
  cur=out/gcur_$k.edges
  echo "n=$n $(../bin/score37 $cur | sed 's/.*far=\([0-9]*\).*/far=\1/')"
done
echo GROWDONE
