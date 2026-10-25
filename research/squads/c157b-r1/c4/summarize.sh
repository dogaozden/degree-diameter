#!/bin/bash
# score every orbit-search output with the official checker and print one line per group
cd /home/user/degree-diameter/research/squads/c157b-r1/c4
for f in out_*.txt; do
  name=${f#out_}; name=${name%.txt}
  res=$(timeout 300 nice -n 10 python3 /home/user/degree-diameter/research/squads/c157b-r1/shared/chkset.py P "$f" 2>&1 | tail -1)
  echo "$name $res"
done
