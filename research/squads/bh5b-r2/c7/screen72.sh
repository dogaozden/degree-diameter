#!/bin/sh
# order-72 screen (432 vertices with a 3+3 base): 4 two-rich nonabelian groups x 4 bases, INC annealer 8 s each
cd /home/user/degree-diameter/research/squads/bh5b-r2/c7
while [ ! -f runs/long64.done ]; do sleep 3; done
VL=/home/user/degree-diameter/research/beyond-haar-d5b/src/vl
for g in 49 17 33 6; do
  for k in 9 8 4 5; do
    r=$(INC=1 D=5 SECS=8 SEED=1 OUT=runs/s72_b${k}_g${g}.sol timeout 60 nice -n 10 $VL bases/b$k.txt grp/sg_72_$g.txt 2>/dev/null | grep RESULT)
    echo "order72 group $g base $k $r"
  done
done
echo DONE72 >> runs/screen72.log
