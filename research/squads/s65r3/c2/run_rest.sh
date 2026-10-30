#!/bin/bash
cd /home/user/degree-diameter/research/squads/s65r3/c2
for id in $(cat /home/user/degree-diameter/research/s65/haar/list_r3_1.txt); do
  [ "$id" = "360_64" ] && continue
  ./run_group.sh "$id"
done
echo ALLDONE
