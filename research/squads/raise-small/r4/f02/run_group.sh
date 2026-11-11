#!/bin/bash
# usage: run_group.sh N m k r SEED...   (one group, sequential seeds; appends "N m k r seed cost" to results.txt)
F=/home/user/degree-diameter/research/squads/raise-small/r4/f02
RS=/home/user/degree-diameter/research/frontier/raise_small
N=$1; m=$2; k=$3; r=$4; shift 4
cd $RS || exit 1
timeout 100 nice -n 10 python3 tools/gtab.py $F/g.tab $m $k $r >/dev/null 2>&1
for s in "$@"; do
  D=13 timeout 100 nice -n 10 $RS/bin/salift_s 2 $F/g.tab 1 $s 13 10 0.3 $F/o_${m}_${k}_${r}_${s}.sol > $F/log_${m}_${k}_${r}_${s}.txt 2>&1
  c=$(head -1 $F/o_${m}_${k}_${r}_${s}.sol.best 2>/dev/null | awk '{print $4}')
  echo "$N $m $k $r $s ${c:-NA}" >> $F/results.txt
  if [ -f $F/o_${m}_${k}_${r}_${s}.sol ]; then echo "FOUND cost0 $N $m $k $r $s" >> $F/results.txt; fi
done
rm -f $F/g.tab
