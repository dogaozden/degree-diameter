#!/bin/sh
# screen: all 10 3+3 bases x 3 two-rich nonabelian groups of order 64 (INC annealer, 8 s each)
cd /home/user/degree-diameter/research/squads/bh5b-r2/c7
VL=/home/user/degree-diameter/research/beyond-haar-d5b/src/vl
for g in 52 202 211; do
  for k in 0 1 2 3 4 5 6 7 8 9; do
    r=$(INC=1 D=5 SECS=8 SEED=1 OUT=runs/s64_b${k}_g${g}.sol timeout 60 nice -n 10 $VL bases/b$k.txt grp/sg_64_$g.txt 2>/dev/null | grep RESULT)
    echo "order64 group $g base $k $r"
  done
done
