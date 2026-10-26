#!/bin/bash
# run.sh FROM TO : farm specs FROM..TO (1-based lines of specs.txt), 4 seeds x 6 s each, K=16 COOL=10 REHEAT=40
FARM=/home/user/degree-diameter/research/squads/hunt-d5/tools/farm.sh
cd /home/user/degree-diameter/research/squads/hunt-d5/r5/b6
i=0
sed -n "$1,$2p" specs.txt | while read mu N tag p k r n rest; do
  dir=/home/user/degree-diameter/research/squads/hunt-d5/r5/b6/g_${p}_${k}_${r}_${n}
  mkdir -p "$dir"
  start=$(date +%s)
  COOL=10 REHEAT=40 timeout 150 nice -n 10 "$FARM" "$dir" 7 6 16 61001 4 meta $p $k $r $n
  echo "spec=meta_${p}_${k}_${r}_${n} order=$N wall=$(( $(date +%s)-start ))s" >> b6_timing.log
done
echo BATCH_DONE $1 $2 >> b6_timing.log
