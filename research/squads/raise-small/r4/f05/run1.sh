#!/bin/bash
# usage: run1.sh m k r SEED  (one salift_s run, D=14, p=3, 13 CPU-s), appends to results.txt
cd /home/user/degree-diameter/research/squads/raise-small/r4/f05
RS=/home/user/degree-diameter/research/frontier/raise_small
m=$1; k=$2; r=$3; S=$4
G=g_${m}_${k}_${r}.tab
[ -f $G ] || python3 $RS/tools/gtab.py $G $m $k $r >/dev/null
N=$((m*k))
D=14 timeout 100 nice -n 10 $RS/bin/salift_s 3 $G 1 $S 13 10 0.3 o_${m}_${k}_${r}_$S.sol > log_${m}_${k}_${r}_$S.txt 2>&1
c=$(head -1 o_${m}_${k}_${r}_$S.sol.best 2>/dev/null | awk '{print $4}')
echo "$N $m $k $r $S ${c:-NA}" >> results.txt
