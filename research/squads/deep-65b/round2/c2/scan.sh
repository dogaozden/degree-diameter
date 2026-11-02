#!/bin/bash
# c2 driver (round 2, card c2). usage: scan.sh TODO   (TODO lines: "ORDER ID SEED", runs shared/tabu15 12 s each)
# Appends "ORDER ID SEED | RES line" to raw.txt. Skips runs already in raw.txt. Starts no new run after 90 s of this call.
D=/home/user/degree-diameter/research/squads/deep-65b/round2/c2
G=/home/user/degree-diameter/research/squads/deep-65b/groups
RS=/home/user/degree-diameter/research/squads/deep-65b/shared
SECS=${SECS:-12}
START=$(date +%s)
touch $D/raw.txt
while read ord id seed; do
  [ -z "$ord" ] && continue
  if grep -q "^$ord $id $seed |" $D/raw.txt; then continue; fi
  el=$(( $(date +%s) - START ))
  if [ $el -gt 90 ]; then break; fi
  tab=$G/sg_${ord}_${id}.tab
  [ -f "$tab" ] || tab=$D/tabs/sg_${ord}_${id}.tab
  line=$(timeout 30 nice -n 15 $RS/tabu15 $tab $seed $SECS $D/edges/sg_${ord}_${id}_s${seed}.edges)
  echo "$ord $id $seed | $line" >> $D/raw.txt
done < "$1"
echo "calls done: $(wc -l < $D/raw.txt) runs in raw.txt; pending in $1: $(grep -c . "$1") lines in todo"
