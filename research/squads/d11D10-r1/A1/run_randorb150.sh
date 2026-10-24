#!/bin/bash
# A1: RANDORB=150 on the three k = 5 PSL groups (more samples than the 30 of run_randorb.sh), run after the anneal.
D=/home/user/degree-diameter/research/squads/d11D10-r1
A=$D/A1
G=$D/gate.sh
H=/home/user/degree-diameter/research/structured/haar_sym
cd "$A" || exit 1
for spec in "41 2161" "61 661" "41 2201"; do
  set -- $spec
  tag="psl_$1_$2"
  echo "$(date -u +%T) start $tag" >> "$A/randorb150_driver.log"
  "$G" 121 env THREADS=1 ORBIT="5 2 1" RANDORB=150 "$H" 11 10 1 1 8 /dev/null psl "$1" "$2" > "$A/randorb150_$tag.log" 2>&1
  rc=$?
  echo "rc=$rc" >> "$A/randorb150_$tag.log"
  echo "$(date -u +%T) done $tag rc=$rc" >> "$A/randorb150_driver.log"
done
echo "$(date -u +%T) all done" >> "$A/randorb150_driver.log"
