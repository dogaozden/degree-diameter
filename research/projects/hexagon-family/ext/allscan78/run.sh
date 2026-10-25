#!/bin/bash
# all-lines extension scan (ext_all.py) at q = 7 (R 288, bar 296) and q = 8 (R 217, bar 232), several seeds/orders
cd /home/user/degree-diameter/research/projects/hexagon-family/ext
S=../../../d10D7/sets
for s in 1 2 3 4 5 6; do
  for o in ovl nx; do
    timeout 900 nice -n 19 python3 ext_all.py 7 $S/P7_c5_288.txt $S/L7_c5_344.txt allscan78/q7_${o}_s$s $s $o 100 800 2>&1 | grep RESULT >> allscan78/q7.log
    timeout 900 nice -n 19 python3 ext_all.py 8 $S/P8_r5c4_217.txt $S/L8_spread513.txt allscan78/q8_${o}_s$s $s $o 100 800 2>&1 | grep RESULT >> allscan78/q8.log
  done
done
echo DONE >> allscan78/q7.log
