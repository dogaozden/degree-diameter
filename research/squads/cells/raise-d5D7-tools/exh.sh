#!/bin/bash
# usage: exh.sh LINE... ; each arg: "N|spec|AR"  (AR empty = default alpha). Exhaustive-ish RANDORB screen.
S=/home/user/degree-diameter/research/structured/haar_sym
SP=/tmp/claude-0/-home-user-degree-diameter/dc574623-c6c6-5598-9b3e-ade6117641a7/scratchpad
for line in "$@"; do
  IFS='|' read -r N spec ar <<< "$line"
  envs="ORBIT=3_1_2"; [ -n "$ar" ] && envs="$envs AR=$ar"
  tag=$(echo "${spec}_AR${ar:-d}" | tr ' ' '_')
  out=$(env ORBIT="3 1 2" ${ar:+AR=$ar} RANDORB=300000 timeout 250 $S 5 7 1 1 8 $SP/sols/x_$tag.txt $spec 2>&1)
  res=$(echo "$out" | grep "^RANDORB d=" | sed 's/.*group=//; s/ time=.*//')
  zero=$(echo "$out" | grep -c "has cost 0")
  echo "[$spec AR=${ar:-default}] ${res:-NORESULT} zero=$zero"
done
