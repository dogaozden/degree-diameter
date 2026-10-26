#!/bin/bash
# one lift job: "BASE|GROUP" -> 120 s anneal, seed 1; log the RESULT line
IFS='|' read -r base grp <<< "$1"
tag=$(basename $base .txt)_$(echo $grp | tr ' ' '_')
cd /home/user/degree-diameter/research/fresh65/lifts33
timeout 150 ../tools/lift search $base 5 60 1 8 sols/$tag.sol $grp > logs/$tag.log 2>&1
grep RESULT logs/$tag.log | sed "s|^|$tag |" >> results.txt
