#!/bin/bash
W=/home/user/degree-diameter/research/squads/own-small/r1/w1
L=/home/user/degree-diameter/tools/bin/lift
L=/home/user/degree-diameter/research/squads/own-small/tools/bin/lift
for pair in thetaS:t406_1 dumbbell:t406_2 thetaS:t444_8 thetaS:t410_1 dumbbell:t406_1; do
  b=${pair%%:*}; g=${pair##*:}
  $L $W/bases/$b.txt $W/groups/$g.txt 3 10 60 11 8 $W/out/push_${b}_${g} 2>&1 | grep RESULT | tail -1 >> $W/out/push.txt
done
echo DONE >> $W/out/push.txt
