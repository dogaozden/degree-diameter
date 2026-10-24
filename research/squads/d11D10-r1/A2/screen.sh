#!/bin/bash
# A2 RANDORB screen: k = 5, ORBIT="5 2 1", 30 random symmetric S per group, one after another inside one gate slot.
H=/home/user/degree-diameter/research/structured/haar_sym
D=/home/user/degree-diameter/research/squads/d11D10-r1/A2
for spec in "89 211" "71 421" "79 311"; do
  set -- $spec
  env ORBIT="5 2 1" RANDORB=30 "$H" 11 10 1 1 8 /dev/null psl "$1" "$2" > "$D/randorb_psl$1_$2.log" 2>&1
  echo "done psl $1 x Z$2 rc=$?" >> "$D/screen_status.log"
done
