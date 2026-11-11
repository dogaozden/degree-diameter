#!/bin/bash
# usage: chain.sh m k r STARTFILE SEED  -> salift_s chained from a cost<=4 state, T0=4, 13 CPU-s, D=14
cd /home/user/degree-diameter/research/squads/raise-small/r4/f05
RS=/home/user/degree-diameter/research/frontier/raise_small
m=$1; k=$2; r=$3; ST=$4; S=$5
G=g_${m}_${k}_${r}.tab
[ -f $G ] || python3 $RS/tools/gtab.py $G $m $k $r >/dev/null
N=$((m*k))
START=$ST D=14 timeout 100 nice -n 10 $RS/bin/salift_s 3 $G 1 $S 13 4 0.3 ch_${m}_${k}_${r}_$S.sol > logch_${m}_${k}_${r}_$S.txt 2>&1
c=$(head -1 ch_${m}_${k}_${r}_$S.sol.best 2>/dev/null | awk '{print $4}')
echo "$N $m $k $r chain$S(from $ST) ${c:-NA}" >> results.txt
rm -f $G
