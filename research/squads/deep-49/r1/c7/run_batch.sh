#!/bin/bash
# usage: run_batch.sh NAME...   (NAME = exp file base name); LIMIT 0, one hx run per group
T=/home/user/degree-diameter/research/squads/deep-49/tools
D=/home/user/degree-diameter/research/squads/deep-49/r1/c7
cd $D
for b in "$@"; do
  s=$(date +%s)
  timeout 100 nice -n 10 python3 $T/build_tab.py exp/$b.exp w/$b > /dev/null 2>&1 || { echo "$b BUILD_FAIL"; continue; }
  timeout 100 nice -n 10 $T/hx w/$b.tab w/$b.aut 0 9 > res/$b.out 2> res/$b.err
  rc=$?
  e=$(date +%s)
  line="$b rc=$rc secs=$((e-s)) $(grep -h 'x-orbits' res/$b.err | sed 's/.*x-orbits=//;s/(excluding.*//') $(tail -1 res/$b.out)"
  echo "$line" | tee -a res/summary.txt
  rm -f w/$b.tab
done
