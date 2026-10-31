#!/bin/bash
# runs the families in families.txt one after another (one heavy process at a time), nice -n 10
cd /home/user/degree-diameter/research/squads/handsoff-108/c5b-cosetscreen
mkdir -p out
while read name q psl htype h spec split sdet K seed; do
  case "$name" in \#*|"") continue;; esac
  if [ -s out/$name.out ] && grep -q "^cand $((K-1)) " out/$name.out; then continue; fi
  SPLIT=$split SDET=$sdet DEG=10 TT=8 timeout 3000 nice -n 10 ./cscreen $q $psl $htype $h $spec $K $seed > out/$name.out 2> out/$name.err
  echo "$name done $(date -u +%H:%M:%S) rc=$?" >> out/progress.log
done < families.txt
echo "all done $(date -u +%H:%M:%S)" >> out/progress.log
