#!/bin/bash
# after the group screen: ILS on 2+2 multigraph bases (n = 4k) and K44/PG(2,3) baselines
cd /home/user/degree-diameter/research/squads/handsoff-49/w4
while ! grep -q DONE run_groups.log; do sleep 5; done
for k in 1243 1245 1250; do
  for b in b22t1 b22t2; do
    ILS=1 nice -n 10 ./hgi $b.txt cyc:$k 90 31 1 1 ils_${b}_$k 2>&1 | grep -E "ILS sweeps|RESULT" | sed "s/^/$b k=$k /"
  done
done
ILS=1 nice -n 10 ./hgi k44.txt cyc:622 120 21 1 1 ils_k44_z622 2>&1 | grep -E "RESULT" | sed 's/^/K44 Z622 /'
ILS=1 nice -n 10 ./hgi pg23.txt cyc:192 120 25 1 1 ils_pg_z192 2>&1 | grep -E "RESULT" | sed 's/^/PG Z192 /'
echo DONE_ILS2
