#!/bin/bash
cd /home/user/degree-diameter/research/squads/f65r1/c2
seed=100
while IFS='|' read -r h g spec base; do
  seed=$((seed+1))
  s=${spec// /_}
  echo "$h|$g|$s|$base|30|$seed"
done < screen_jobs.txt | xargs -P 2 -I{} ./run_one.sh {}
echo done > screen_done.flag
