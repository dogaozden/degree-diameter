#!/bin/bash
# usage: grp.sh m k r  -> seeds 1 and 2 via run1.sh, then delete the group table
cd /home/user/degree-diameter/research/squads/raise-small/r4/f05
m=$1; k=$2; r=$3
./run1.sh $m $k $r 1
./run1.sh $m $k $r 2
rm -f g_${m}_${k}_${r}.tab
