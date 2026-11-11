#!/bin/bash
# usage: screen.sh p m k r secs seed  (env D=14). Builds table, runs salift_s, checks any find, deletes table.
RS=/home/user/degree-diameter/research/frontier/raise_small
W=/home/user/degree-diameter/research/squads/raise-small/r1/c06
p=$1; m=$2; k=$3; r=$4; secs=$5; seed=$6
tag=${m}_${k}_${r}_p${p}_s${seed}
printf "%d %d %d\n" $m $k $r > $W/t_$tag.lst
cd $W && timeout 100 nice -n 10 python3 $RS/tools/gtab.py $W/t_$tag.tab --list $W/t_$tag.lst 2>/dev/null
N=$((m*k))
D=14 timeout 100 nice -n 10 $RS/bin/salift_s $p $W/t_$tag.tab 1 $seed $secs 10 0.3 $W/s_$tag.sol 2>&1 | tail -2
rm -f $W/t_$tag.tab
if [ -f $W/s_$tag.sol ]; then
  timeout 100 nice -n 10 python3 $RS/tools/sol2edges.py $W/s_$tag.sol $m $k $r $W/e_$tag.edges && timeout 100 nice -n 10 $RS/bin/apsp $W/e_$tag.edges 3 14 | tail -1
  rm -f $W/e_$tag.edges
fi
