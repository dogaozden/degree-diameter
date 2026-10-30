#!/bin/bash
# sweep1.sh: symmetric lift screen (sym22, DELTA=7) over groups given as args (N_ID), a = 1..6, SECS per beta
cd /home/user/degree-diameter/research/squads/d75-r2/c2
for g in "$@"; do
  for a in 1 2 3 4 5 6; do
    r=$(DELTA=7 SECS=${SECS:-1} timeout 400 nice -n 15 ./sym22 tmp/g${g}.ht $a tmp/hit_${g}_a$a.edges 2>&1)
    echo "== $g a $a"; echo "$r" | grep -E "RESULT|HIT|DONE" | awk '/RESULT/{print} /HIT|DONE/{print}' | sed -n 1,200p
  done
done
echo SWEEP DONE
