#!/bin/bash
# usage: timeout 105 nice -n 15 bash scan.sh   (foreground, resumable)
# tabu15f on the 12 order-192 groups of card c3, seed-major order (seeds 1..12, each seed over all groups, 12 s each).
# Starts no new run after 85 s of this call, so the call stays under 105 s. Appends "id seed best t_best" to raw.txt,
# the full RES line to runs/all.txt, and "HIT id seed" to hits/HITS.txt when best=0 (edges in hits/).
D=/home/user/degree-diameter/research/squads/deep-65b/round3/c3
IDS="845 931 900 168 934 916 58 171 861 22 351 978"
touch $D/raw.txt $D/runs/all.txt $D/hits/HITS.txt
START=$(date +%s)
for seed in $(seq 1 12); do
  for id in $IDS; do
    if grep -q "^$id $seed " $D/raw.txt; then continue; fi
    el=$(( $(date +%s) - START ))
    if [ $el -ge 90 ]; then echo "stopped at elapsed ${el}s, rerun to continue"; exit 0; fi
    line=$($D/tabu15f $D/tabs/sg_192_${id}.tab $seed 12 $D/hits/e192_${id}_s${seed}.edges)
    best=$(echo "$line" | sed -n 's/.* best=\([0-9]*\) .*/\1/p')
    tb=$(echo "$line" | sed -n 's/.* t_best=\([0-9.]*\) .*/\1/p')
    echo "$id $seed ${best:-ERR} ${tb:-ERR}" >> $D/raw.txt
    echo "$id $line" >> $D/runs/all.txt
    if [ "$best" = "0" ]; then echo "HIT id=$id seed=$seed" >> $D/hits/HITS.txt; fi
  done
done
echo "all 144 runs done"
