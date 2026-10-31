#!/bin/bash
# runs groups from remain.txt starting at the pointer in next.txt until ~240 s elapsed (foreground only)
C15=/home/user/degree-diameter/research/squads/handsoff-65/c15
SECS=${SECS:-6}; START=$(cat $C15/next.txt 2>/dev/null || echo 1); T0=$SECONDS; i=$START
while [ $((SECONDS-T0)) -lt 240 ]; do
  line=$(sed -n "${i}p" $C15/remain.txt); [ -z "$line" ] && break
  set -- $line
  $C15/sweep15.sh $SECS $1 $2
  i=$((i+1)); echo $i > $C15/next.txt
done
echo "pointer $i of $(wc -l < $C15/remain.txt) at $(date -u +%H:%M)"
