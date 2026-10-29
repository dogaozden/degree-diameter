#!/bin/bash
# c1 screen: one group per order (non-abelian first, cyclic where only abelian exists), a in 1,2,3; 15 s per run.
C=/home/user/degree-diameter/research/squads/bh5-r1/c1
VL=/home/user/degree-diameter/research/beyond-haar-d5/vl
cd /home/user/degree-diameter/research/beyond-haar-d5
for g in 290_1 291_1 292_1 293_1 294_1 295_1 296_1 297_3 298_1 299_1 300_1; do
  for a in 2 1 3; do
    tag=g${g}_a${a}
    res=$(D=5 SECS=15 ITERS=70000 SEED=1 T0=3 T1=0.2 OUT=$C/sols/$tag.sol timeout 60 nice -n 10 $VL $C/bases/b4_a$a.txt $C/groups/sg_$g.txt 2>$C/logs/$tag.log | grep RESULT)
    echo "$g a=$a $res" >> $C/logs/screen.txt
  done
done
echo DONE >> $C/logs/screen.txt
