#!/bin/bash
# driver.sh: run run1.sh sequentially over order.txt (fewest involutions first), one group at a time.
cd /home/user/degree-diameter/research/squads/d75-r1/c5
export LOGDIR=/home/user/degree-diameter/research/squads/d75-r1/c5/logs
export CANDDIR=/home/user/degree-diameter/research/squads/d75-r1/c5/cand
export TMPDIR=/home/user/degree-diameter/research/squads/d75-r1/c5/tmp
export MAXEV=10000000 GAPT=180 EXHT=600
while read N ID INV; do
  timeout 900 nice -n 10 /home/user/degree-diameter/research/d75-raise/src/run1.sh $N $ID
done < order.txt
echo "DRIVER DONE" >> logs/sweep.txt
