#!/bin/bash
# usage: run.sh N m k r SEED...   (one group, fresh seeds; appends "N m k r seed cost" to results.txt)
# Wall guard: the whole call stays under ~100 s; a seed that gets no time is recorded as SKIP.
R=/home/user/degree-diameter/research/frontier/raise_small
cd /home/user/degree-diameter/research/squads/raise-small/r4/f01
N=$1; m=$2; k=$3; r=$4; shift 4
T0=$(date +%s)
python3 $R/tools/gtab.py g.tab $m $k $r >/dev/null || exit 1
for seed in "$@"; do
  left=$(( 98 - ($(date +%s) - T0) ))
  if [ $left -lt 25 ]; then echo "$N $m $k $r $seed SKIP" >> results.txt; continue; fi
  f=o_${m}_${k}_${r}_${seed}.sol
  D=13 timeout $left nice -n 10 $R/bin/salift_s 2 g.tab 1 $seed 13 10 0.3 $f >/dev/null 2>&1
  c=$(head -1 $f.best | awk '{print $4}')
  echo "$N $m $k $r $seed ${c:-NA}" >> results.txt
  [ -f $f ] && echo "  COST0 FILE $f"
done
rm -f g.tab
