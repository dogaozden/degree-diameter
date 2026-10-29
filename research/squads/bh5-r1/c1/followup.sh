#!/bin/bash
# c1 follow-up: longer runs (SECS=60) on the best screen candidates, one at a time.
C=/home/user/degree-diameter/research/squads/bh5-r1/c1
VL=/home/user/degree-diameter/research/beyond-haar-d5/vl
cd /home/user/degree-diameter/research/beyond-haar-d5
for spec in "$@"; do
  g=${spec%:*}; a=${spec#*:}
  tag=long_g${g}_a${a}
  res=$(D=5 SECS=60 ITERS=250000 SEED=7 T0=3 T1=0.2 OUT=$C/sols/$tag.sol timeout 90 nice -n 10 $VL $C/bases/b4_a$a.txt $C/groups/sg_$g.txt 2>$C/logs/$tag.log | grep RESULT)
  echo "LONG $g a=$a $res" >> $C/logs/followup.txt
done
echo DONE >> $C/logs/followup.txt
