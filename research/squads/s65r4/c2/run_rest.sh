#!/bin/bash
# sequential exhaustive haarex2 runs for the remaining s65r4 c2 groups (one process at a time)
cd /home/user/degree-diameter/research/squads/s65r4/c2
for i in 64 84 100 139 154; do
  gap -q -c "K:=SmallGroup(352,$i);; FN:=\"hx_352_$i.txt\";;" /home/user/degree-diameter/research/s65/tools/haarex2.g > export_$i.log 2>&1
  timeout 1200 nice -n 10 env THREADS=1 /home/user/degree-diameter/research/s65/tools/haarex2 hx_352_$i.txt > h352_$i.log 2>&1
  echo "EXIT $?" >> h352_$i.log
  rm -f hx_352_$i.txt
done
echo ALLDONE > rest_done.txt
