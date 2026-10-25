#!/bin/bash
# usage: verify_volt.sh BASE GROUPNAME VOLT TAG   (BASE relative to the chartlift dir; VOLT as printed by ctrl_search/ctrl_exh)
F=/home/user/degree-diameter/research/squads/r2-chartlift/c6; C=/home/user/degree-diameter/research/theorems/chartlift
cd $C
base=$1; g=$2; volt=$3; tag=$4
cost=$(VOLT=$volt timeout 300 nice -n 10 $F/ctrl_search $base $F/gtab/$g.txt $F/c4s2.flags 1 1 $F/lifts/$tag | head -1 | sed 's/.*cost=\([0-9]*\).*/\1/')
m=$(head -1 $F/lifts/$tag.ctrl)
timeout 300 nice -n 10 python3 lift.py $F/lifts/$tag.ctrl charts/c4s2_k4_q2.txt 2 4 $F/lifts/$tag.edges > /dev/null
res=$(timeout 600 nice -n 10 $F/apsp $F/lifts/$tag.edges 8 5 | tr '\n' ' ')
rm -f $F/lifts/$tag.edges
echo "$tag base=$base group=$g m=$m cost=$cost :: $res"
