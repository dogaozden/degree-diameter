#!/bin/bash
# (4,9): quartic joint lifts over ODD-order groups (no involutions), salift4, 60 CPU-s per run
cd /home/user/degree-diameter/research/frontier/raise_small; mkdir -p runs/Q49
run() { p=$1; m=$2; k=$3; r=$4; s=$5; tab=runs/Q49/g_${m}_${k}_${r}.tab
  [ -f $tab ] || python3 tools/gtab.py $tab $m $k $r 2>/dev/null
  out=runs/Q49/q_${p}_${m}_${k}_${r}_s$s.sol
  D=9 CYC=60 timeout 900 bin/salift4 $p $tab 1 $s 60 10 0.3 $out > /dev/null
  echo "p=$p meta $m $k $r N=$((m*k)) n=$((2*p*m*k)) seed=$s cost=$(head -1 $out.best | awk '{print $4}') $([ -f $out ] && echo FOUND)" >> runs/Q49/q49.log; }
run 2 23 55 2 1; run 3 43 21 9 1; run 2 115 11 6 1; run 3 61 15 12 1; run 2 23 55 2 2; run 3 43 21 9 2
