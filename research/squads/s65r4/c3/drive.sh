#!/bin/bash
# card c3: exhaustive haarex2 over the assigned groups, one process at a time, 33-minute overall deadline
cd /home/user/degree-diameter/research/squads/s65r4/c3
DEADLINE=$(( $(cat start_epoch.txt) + 33*60 ))
TOOLS=/home/user/degree-diameter/research/s65/tools
for g in "352 163" "354 1" "360 23" "360 93" "360 103" "360 113" "360 125" "360 136"; do
  set -- $g; o=$1; i=$2; tag=${o}_${i}
  now=$(date +%s); rem=$(( DEADLINE - now ))
  if [ $rem -lt 60 ]; then echo "SKIP $tag (deadline)" >> run_order.log; continue; fi
  tl=$(( rem < 1200 ? rem : 1200 ))
  echo "START $tag $(date +%T) timeout=$tl" >> run_order.log
  gap -q -c "K:=SmallGroup($o,$i);; FN:=\"hx_$tag.txt\";;" $TOOLS/haarex2.g > exp_$tag.log 2>&1
  echo "EXPORT $(cat exp_$tag.log | tail -1)" >> run_order.log
  timeout $tl nice -n 10 $TOOLS/haarex2 hx_$tag.txt > h$tag.log 2>&1
  echo "END $tag rc=$? $(date +%T) lastline=$(tail -1 h$tag.log)" >> run_order.log
  rm -f hx_$tag.txt
done
echo ALLDONE $(date +%T) >> run_order.log
