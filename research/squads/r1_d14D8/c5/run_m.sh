#!/bin/bash
# usage: run_m.sh TAG HEXMODE PSIMODE SEEDF SEEDM m1 m2 ...   (builds work/TAG_m.txt, evaluates with liftevalw r:20:1)
TAG=$1; HEX=$2; PSI=$3; SF=$4; SM=$5; shift 5
cd /home/user/degree-diameter/research/squads/r1_d14D8/c5
for m in "$@"; do
  f=work/${TAG}_m${m}.txt
  timeout 900 nice -n 10 python3 mkd.py $f $m $SF $SM $HEX $PSI ${TAG} > /dev/null 2>&1 || { echo "build failed m=$m"; continue; }
  res=$(cd /home/user/degree-diameter/research/squads/cells/d14D8_work && timeout 900 nice -n 10 ./liftevalw /home/user/degree-diameter/research/squads/r1_d14D8/c5/$f 8 r:20:1 2>/dev/null)
  echo "$TAG m=$m $res"
  rm -f $f
done
