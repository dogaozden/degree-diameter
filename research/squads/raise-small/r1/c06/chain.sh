#!/bin/bash
# usage: chain.sh p m k r secs seed : table build, then salift_s (START from prior .best of this group if any), then check on cost 0.
RS=/home/user/degree-diameter/research/frontier/raise_small
W=/home/user/degree-diameter/research/squads/raise-small/r1/c06
p=$1; m=$2; k=$3; r=$4; secs=$5; seed=$6
tag=${m}_${k}_${r}_p${p}
printf "%d %d %d\n" $m $k $r > $W/t_$tag.lst
cd $W && timeout 30 nice -n 10 python3 $RS/tools/gtab.py $W/t_$tag.tab --list $W/t_$tag.lst 2>/dev/null
st=""
if [ -f $W/s_$tag.sol.best ]; then st="START=$W/s_$tag.sol.best"; fi
env $st D=14 timeout 60 nice -n 10 $RS/bin/salift_s $p $W/t_$tag.tab 1 $seed $secs 10 0.3 $W/s_$tag.sol > $W/log_${tag}_$seed.txt 2>&1
rm -f $W/t_$tag.tab
echo "tag=$tag best=$(head -1 $W/s_$tag.sol.best 2>/dev/null) found=$( [ -f $W/s_$tag.sol ] && echo yes || echo no)"
if [ -f $W/s_$tag.sol ]; then
  timeout 30 nice -n 10 python3 $RS/tools/sol2edges.py $W/s_$tag.sol $m $k $r $W/e_$tag.edges && timeout 40 nice -n 10 $RS/bin/apsp $W/e_$tag.edges 3 14 | tail -1
  rm -f $W/e_$tag.edges
fi
