#!/bin/bash
# Card A5 (k = 3, ORBIT="3 3 2" on SL(2,p) x Z_n): RANDORB=30 screens, one gated run per group, in sequence.
G=/home/user/degree-diameter/research/squads/d11D10-r1/gate.sh
H=/home/user/degree-diameter/research/structured/haar_sym
A=/home/user/degree-diameter/research/squads/d11D10-r1/A5
cd "$A" || exit 1
for spec in "61 331" "73 193" "101 73"; do
  set -- $spec
  tag="sl$1_$2"
  "$G" 121 env ORBIT="3 3 2" RANDORB=30 "$H" 11 10 1 5 8 /dev/null sl "$1" "$2" > "$A/randorb_$tag.log" 2>&1
  echo "rc=$? $tag $(date +%T)" >> "$A/screens.done"
done
echo ALLDONE "$(date +%T)" >> "$A/screens.done"
