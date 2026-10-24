#!/bin/bash
# usage: run_r.sh TAG MATCHMODE HEXMODE m1 m2 ...
TAG=$1; MM=$2; HM=$3; shift 3
cd /home/user/degree-diameter/research/squads/r1_d14D8/c5
for m in "$@"; do
  f=work/${TAG}_m${m}.txt
  timeout 900 nice -n 10 python3 mkr.py $f $m 1 $MM $HM 0 > /dev/null 2>work/${TAG}_m${m}.log || { echo "build failed $TAG m=$m"; continue; }
  res=$(cd /home/user/degree-diameter/research/squads/cells/d14D8_work && timeout 900 nice -n 10 ./liftevalw /home/user/degree-diameter/research/squads/r1_d14D8/c5/$f 8 r:20:1 2>/dev/null)
  echo "$TAG m=$m $res"
  rm -f $f
done
