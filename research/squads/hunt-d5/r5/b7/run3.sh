#!/bin/bash
# run3.sh: extra seeds 7-13 (7 x 6 s) on the three best groups (cost 6 so far)
cd /home/user/degree-diameter/research/squads/hunt-d5/r5/b7
for dir in g609_p29_k7_r16_n3:29:7:16:3 g615_p41_k5_r10_n3:41:5:10:3 g618_p103_k3_r56_n2:103:3:56:2; do
  IFS=: read d p k r n <<< "$dir"
  COOL=10 REHEAT=40 timeout 400 nice -n 10 ../../tools/farm.sh $PWD/$d 7 6 16 7 7 meta $p $k $r $n
done
echo ALLDONE3
