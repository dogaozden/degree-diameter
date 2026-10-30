#!/bin/bash
# card c5: sequential exhaustive Haar runs, 120 s budget each, one process at a time
cd /home/user/degree-diameter/research/squads/s65r6/c5
for ID in "378 16" "378 24" "378 25" "372 10" "380 1" "368 21" "368 26" "378 2" "366 3" "378 46" "378 33"; do
  set -- $ID; O=$1; I=$2
  gap -q -c "K:=SmallGroup($O,$I);; FN:=\"hx_${O}_${I}.txt\";;" /home/user/degree-diameter/research/squads/s65r6/c5/haarex2.g > exp_${O}_${I}.out 2>&1
  timeout 120 nice -n 10 ./haarex2 hx_${O}_${I}.txt > h${O}_${I}.log 2>&1
  echo "exit=$? $O $I" >> driver.log
  rm -f hx_${O}_${I}.txt
done
echo ALLDONE >> driver.log
