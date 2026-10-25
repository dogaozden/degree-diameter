#!/bin/bash
# usage: run_batch.sh SECONDS name1 name2 ... ; runs orbitclique13 on perms/perm_NAME.txt, one heavy slot at a time
S=$1; shift
cd /home/user/degree-diameter/research/squads/d14D7-r4/c4
for nm in "$@"; do
  THREADS=1 /home/user/degree-diameter/research/squads/bin/heavy.sh 200 ./orbitclique13 /home/user/degree-diameter/research/cell147/data/E13.map perms/perm_${nm}.txt $S 1 flags/flags_q13_${nm}.txt > logs/${nm}.log 2>&1
  echo "$nm rc=$? $(grep -E '^best' logs/${nm}.log)" 
done
