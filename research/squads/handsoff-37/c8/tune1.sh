#!/bin/bash
cd /home/user/degree-diameter/research/squads/handsoff-37/c8
for cfg in "3 1 0.5 2" "4 1 0.5 2" "5 0.5 0.5 2" "5 2 0.5 2" "5 1 0.5 1" "5 1 0.2 2"; do
  set -- $cfg
  echo "== s=$1 T=$2 pb=$3 R=$4"
  nice -n 10 ./lns 150 7 30 $1 $2 $3 $4 out/c150t 2>/dev/null
done
