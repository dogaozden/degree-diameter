#!/bin/bash
cd /home/user/degree-diameter/research/squads/bh5b-r2/c6
VL=/home/user/degree-diameter/research/beyond-haar-d5b/src/vl
for g in 544_221 528_167; do
  r=$(D=5 SECS=120 SEED=1 OUT=sol/long1_b44_$g.txt timeout 900 nice -n 10 $VL b44.txt grp/sg_$g.txt | grep RESULT)
  echo "long b44 $g $r"
done
echo LONGDONE
