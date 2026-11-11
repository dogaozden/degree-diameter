#!/bin/bash
# usage: run_group.sh N m k r seed [seed...]   (runs salift_s D=12, p=2, one run per seed, 11 CPU-s each)
F=/home/user/degree-diameter/research/squads/raise-small/r4/f06
RS=/home/user/degree-diameter/research/frontier/raise_small
N=$1; m=$2; k=$3; r=$4; shift 4
G=$F/g_${m}_${k}_${r}.tab
python3 -I $RS/tools/gtab.py $G $m $k $r >/dev/null 2>&1 || exit 1
for s in "$@"; do
  D=12 timeout 100 nice -n 10 $RS/bin/salift_s 2 $G 1 $s 11 10 0.3 $F/o_${m}_${k}_${r}_${s}.sol > $F/log_${m}_${k}_${r}_${s}.txt 2>&1
  c=$(head -1 $F/o_${m}_${k}_${r}_${s}.sol.best 2>/dev/null | awk '{print $4}')
  echo "$N $m $k $r $s $c"
done
rm -f $G
