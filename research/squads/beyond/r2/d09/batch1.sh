#!/bin/bash
# usage: batch1.sh SECS D ; each line: name|d|GROUP... n
cd "$(dirname "$0")"
SECS=$1; D=$2; shift 2
while IFS='|' read -r name dd grp; do
  [ -z "$name" ] && continue
  ORBIT="${ORB:-3 1 1}" THREADS=1 timeout 900 nice -n 10 ./haar_sym $dd $D $SECS ${SEED:-1} 8 sol_${name}.txt $grp > log_${name}.txt 2>&1
  echo "$name: $(grep RESULT log_${name}.txt)"
done
