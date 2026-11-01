#!/bin/bash
# screen_native.sh SECS SEED : runs haar_tab on native (non-table) group specs listed in specs_native.txt, one at a time
H=/home/user/degree-diameter/research/squads/handsoff-49
W=$H/w1
SECS=${1:-6}; SEED=${2:-1}
while IFS= read -r g; do
  [ -z "$g" ] && continue
  tag=$(echo "$g" | tr ' ' '_')
  out=$(timeout 100 nice -n 10 $H/tools/haar_tab 4 9 $SECS $SEED 8 $W/t/$tag.sol $g 2>&1 | grep RESULT)
  echo "$(date -u +%H:%M) seed=$SEED secs=$SECS | $out" >> $W/res/screen_native.log
done < $W/specs_native.txt
