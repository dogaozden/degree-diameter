#!/bin/bash
# usage: summ.sh PREFIX N : annealer cost, exact checker split of flags (controller-level vs chart-level), apsp verdict
D=/home/user/degree-diameter/research/squads/d12D5-r1/c8; R=/home/user/degree-diameter/research/d12D5
P=$1; N=$2
ann=$(grep -o 'best_cost=[0-9]*' $P.log | cut -d= -f2)
DETAIL=1 $D/exact_cover $P.edges $P.echart $N > $P.exact.txt 2>&1
unc=$(grep -o '= [0-9]*  (unreached' $P.exact.txt | awk '{print $2}')
pc=$(grep '^pair_cost' $P.exact.txt | awk '{print $4}')
ctrl_lvl=$(grep 'flag' $P.exact.txt | awk -v N=$N '{split($6,a,"="); if (a[2]==81*81) c++} END {print c+0}')
chart_lvl=$(grep 'flag' $P.exact.txt | awk '{split($6,a,"="); if (a[2]!=81*81) c++} END {print c+0}')
python3 $R/elift.py $P.edges $P.echart $P.lift.edges >/dev/null
ap=$(timeout 250 nice -n 10 $R/apsp $P.lift.edges 12 5 | tail -1 | cut -c1-40)
rm -f $P.lift.edges
cs=$(python3 $D/ctrl_dist.py $P.edges | sed 's/.*| same-side ordered pairs at controller distance > 4: //' | cut -d'|' -f1)
echo "$P: annealer_cost=$ann exact_flags=$pc (controller-level=$ctrl_lvl, chart-level=$chart_lvl) uncovered_ordered=$unc ctrl_same_side_dist>4=$cs apsp=[$ap]"
