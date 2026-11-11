#!/bin/bash
# usage: runner.sh GROUPFILE START_LINE BUDGET_S SEED
# Runs salift_s (D=14, 12 CPU-s) on each group line "N m k r d fpf" from START_LINE, stopping new groups after BUDGET_S.
RS=/home/user/degree-diameter/research/frontier/raise_small
W=/home/user/degree-diameter/research/squads/raise-small/r5/g04
cd $W || exit 1
GF=$1; start=$2; budget=$3; seed=$4
t0=$(date +%s)
i=0
while read N m k r d f; do
  i=$((i+1))
  [ $i -lt $start ] && continue
  now=$(date +%s)
  if [ $((now-t0)) -ge $budget ]; then echo "STOP_AT_LINE $i"; break; fi
  rm -f o.sol o.sol.best g.tab
  python3 $RS/tools/gtab.py g.tab $m $k $r > /dev/null 2>&1 </dev/null
  D=14 timeout 100 nice -n 10 $RS/bin/salift_s 2 g.tab 1 $seed 12 10 0.3 o.sol > log_${N}_${m}_${k}_${r}_s${seed}.txt 2>&1 </dev/null
  cost=$(head -1 o.sol.best 2>/dev/null | awk '{print $4}')
  echo "$N $m $k $r $seed ${cost:-NA} d=$d line=$i" | tee -a results.txt
  rm -f g.tab
  if [ -f o.sol ]; then
    cp o.sol found_${N}_${m}_${k}_${r}_s${seed}.sol
    python3 $RS/tools/sol2edges.py o.sol $m $k $r out_${N}_${m}_${k}_${r}.edges </dev/null
    timeout 100 nice -n 10 $RS/bin/apsp out_${N}_${m}_${k}_${r}.edges 3 14 </dev/null | tee apsp_${N}_${m}_${k}_${r}.txt
  fi
  rm -f out_*.edges
done < $GF
echo "DONE_SCAN elapsed=$(( $(date +%s)-t0 ))s"
