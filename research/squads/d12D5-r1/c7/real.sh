#!/bin/bash
# real per-edge search: usage real.sh BASE TABLE SECS SEED NAME
# anneals voltages + per-edge chart (mlift_ejoint), starting from the colour chart c3_s1; WRITEBEST keeps near misses.
# if cost 0: lift + independent apsp check.
cd /home/user/degree-diameter/research/squads/d12D5-r1/c7
D=/home/user/degree-diameter/research/d12D5
THREADS=1 WRITEBEST=1 INIT_CHART=$D/charts/c3_s1.txt timeout $(( ${3%.*} * 3 + 120 )) nice -n 10 $D/mlift_ejoint bases/$1.txt tables/$2.txt $3 $4 2.0 0.8 out/$5 > out/$5.log 2>&1
grep best_cost out/$5.log | sed 's/ volt=.*//'
if grep -q "best_cost=0 " out/$5.log && [ -f out/$5.edges ]; then
  python3 $D/elift.py out/$5.edges out/$5.echart out/lift_$5.edges && $D/apsp out/lift_$5.edges 12 5 | tail -3 | tee -a out/$5.log
fi
