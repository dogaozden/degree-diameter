#!/bin/bash
# usage: batch.sh CFGFILE  (lines: name m k alpha sigA sigB secs seed T0 T1 ; '#' lines skipped)
# runs run1.sh for each line sequentially (one heavy process at a time); results in out/results.tsv
cd /home/user/degree-diameter/research/squads/handsoff-37/r3a
while read -r name m k al sa sb secs seed t0 t1; do
  [[ -z "$name" || "$name" == \#* ]] && continue
  timeout 100 ./run1.sh "$name" "$m" "$k" "$al" "$sa" "$sb" "$secs" "$seed" "$t0" "$t1"
done < "$1"
echo BATCH_DONE
