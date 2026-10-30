#!/bin/bash
cd /home/user/degree-diameter/research/squads/bh5b-r2/c6
VL=/home/user/degree-diameter/research/beyond-haar-d5b/src/vl
for g in 544_221 544_223 544_222 544_96 528_169 528_167 528_164 528_148 520_48 520_30 560_67; do
  r=$(D=5 SECS=15 SEED=1 OUT=sol/s1_b44_$g.txt timeout 900 nice -n 10 $VL b44.txt grp/sg_$g.txt | grep RESULT)
  echo "b44 $g $r"
done
echo DONE
