#!/bin/bash
# usage: run_group.sh N m k r SEEDS...   (run from f03 folder; builds g.tab, runs salift_s, deletes g.tab)
F=/home/user/degree-diameter/research/squads/raise-small/r4/f03
RS=/home/user/degree-diameter/research/frontier/raise_small
N=$1; m=$2; k=$3; r=$4; shift 4
cd $F || exit 1
timeout 30 nice -n 10 python3 $RS/tools/gtab.py $F/g.tab $m $k $r >/dev/null 2>&1 || { echo "gtab failed $m $k $r"; exit 1; }
for s in "$@"; do
  D=14 timeout 100 nice -n 10 $RS/bin/salift_s 2 $F/g.tab 1 $s 13 10 0.3 $F/o_${m}_${k}_${r}_${s}.sol >/dev/null 2>&1
  c=$(head -1 $F/o_${m}_${k}_${r}_${s}.sol.best 2>/dev/null | awk '{print $4}')
  ok=""; [ -f $F/o_${m}_${k}_${r}_${s}.sol ] && ok=" SOL_FOUND"
  echo "$N $m $k $r $s ${c:-NA}$ok" | tee -a $F/results.txt
done
rm -f $F/g.tab
