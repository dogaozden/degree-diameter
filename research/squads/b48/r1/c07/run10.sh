#!/bin/bash
# c07: test untested metacyclic groups (N in 1121..1250) picked by the scan rule (ord(r) >= 6, gcd(r-1,m) small)
B=/tmp/claude-0/-home-user-degree-diameter/dc6fd85c-f533-550d-af33-040d4dcb67e6/scratchpad/bin
cd /home/user/degree-diameter/research/squads/b48/r1/c07
for spec in "$@"; do
  set -- $spec
  tag="m$1_k$2_r$3"
  THREADS=1 timeout 120 nice -n 10 $B/haar_fast 4 8 15 1 8 out_$tag.txt meta $1 $2 $3 1 > log_$tag.txt 2>&1
  echo "$tag ($((${1}*${2}))) : $(grep RESULT log_$tag.txt | tail -1)"
done
