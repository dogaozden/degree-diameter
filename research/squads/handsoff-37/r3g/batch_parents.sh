#!/bin/sh
# zero-cost m=80 parents: lift2, 30 s per seed; keeps every zero parent as out/par_SEED.items
cd /home/user/degree-diameter/research/squads/handsoff-37/r3g
for s in $(seq $1 $2); do
  timeout 40 nice -n 10 ./lift2 16 5 0 $s 30 1.5 0.2 2000000 out/par$s > out/par$s.log 2>&1
  c=$(head -1 out/par${s}_best.items 2>/dev/null | sed 's/.*cost=\([0-9]*\).*/\1/')
  echo "seed $s cost $c"
  if [ "$c" = "0" ]; then cp out/par${s}_best.items out/zero_$s.items; fi
done
