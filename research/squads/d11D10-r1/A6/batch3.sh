#!/bin/bash
# A6 batch 3: 200-sample RANDORB for the two inequivalent classes (252 ~ 279, 354 ~ 377).
H=/home/user/degree-diameter/research/structured/haar_sym
W=/home/user/degree-diameter/research/squads/d11D10-r1/A6
cd "$W" || exit 1
for AR in 252 354; do
  env ORBIT="5 2 1" RANDORB=200 AR=$AR "$H" 11 10 1 1 8 /dev/null psl 71 421 > randorb200_AR$AR.log 2>&1
  echo "$(date -u +%T) AR=$AR done" >> batch3.time
done
echo "$(date -u +%T) batch3 finished" >> batch3.time
