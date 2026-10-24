#!/bin/bash
# A6 batch 2: exact ALPHA cross-checks. (g^4, AR=252) should reproduce AR=279 and (g^3, AR=252) should reproduce AR=354.
H=/home/user/degree-diameter/research/structured/haar_sym
W=/home/user/degree-diameter/research/squads/d11D10-r1/A6
cd "$W" || exit 1
for pair in "32915 AR279x" "46624 AR354x"; do
  set -- $pair
  env ORBIT="5 2 1" RANDORB=30 ALPHA=$1 AR=252 "$H" 11 10 1 1 8 /dev/null psl 71 421 > randorb30_ALPHA$1_AR252.log 2>&1
  echo "$(date -u +%T) ALPHA=$1 AR=252 done" >> batch2.time
done
echo "$(date -u +%T) batch2 finished" >> batch2.time
