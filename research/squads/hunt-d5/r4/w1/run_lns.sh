#!/bin/bash
# exact pattern-restricted LNS (plfill) from the 8 starts in starts.txt; 3 steps, 14 CPU-s each
cd /home/user/degree-diameter/research/squads/hunt-d5/r4/w1
i=0
while read c pt f a b c2 d2 e f2 g h j; do
  i=$((i+1))
  set="$a $b $c2 $d2 $e $f2 $g $h $j"
  timeout 200 nice -n 10 ./plfill ../../tables/mt_53_26_16.bin "$set" 3 1 14 > plogs/st_$i.log 2>&1
  echo "start$i c0=$c pat=$pt $(grep RESULT plogs/st_$i.log | cut -c1-60)" >> plogs/summary.txt
done < starts.txt
echo DONE >> plogs/summary.txt
