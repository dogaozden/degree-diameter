#!/bin/bash
# q = 7: ext_all is fast (seconds), so many seeds with random order
cd /home/user/degree-diameter/research/projects/hexagon-family/ext
S=../../../d10D7/sets
for s in $(seq 101 400); do
  timeout 300 nice -n 19 python3 ext_all.py 7 $S/P7_c5_288.txt $S/L7_c5_344.txt allscan78/q7r_s$s $s rand 100 200 2>&1 | grep RESULT >> allscan78/q7r.log
  k=$(tail -1 allscan78/q7r.log | grep -o "= [0-9]*;" | grep -o "[0-9]*")
  [ -n "$k" ] && [ "$k" -le 296 ] && rm -f allscan78/q7r_s$s.pairs
done
echo DONE >> allscan78/q7r.log
