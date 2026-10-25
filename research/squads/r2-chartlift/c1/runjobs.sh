#!/bin/bash
# usage: runjobs.sh SECS SEED GROUPTAG...   (GROUPTAG = file stem in c1/gtab, e.g. meta_20_8_3); sequential, one process
C=/home/user/degree-diameter/research/squads/r2-chartlift/c1
CH=/home/user/degree-diameter/research/theorems/chartlift
cd $CH || exit 1
SECS=$1; SEED=$2; shift 2
for g in "$@"; do
  tag=${g}_s${SEED}_t${SECS}
  res=$(timeout 900 nice -n 10 $C/ctrl_search bases5/k5r1_000.txt $C/gtab/$g.txt r3/k5q3_pd112.flags $SECS $SEED $C/runs/$tag 2>&1 | tail -n 1)
  echo "$g seed=$SEED secs=$SECS | $(echo "$res" | cut -c1-120)" | tee -a $C/runs.log
done
