#!/bin/sh
# summary of split15 exact runs: group, name, E1 classes, solutions, best cost, seconds
cd "$(dirname "$0")/.."
for f in runs/ex_*.txt; do g=$(basename $f .txt); g=${g#ex_}; case $g in *_p*) continue;; esac
  d=$(grep DONE $f); [ -z "$d" ] && { echo "$g RUNNING"; continue; }
  echo "$g $(echo $d | sed 's/.* E1 \([0-9]*\) .*solutions \([0-9]*\) best \([0-9]*\) .*secs \([0-9.]*\)/E1=\1 sol=\2 best=\3 secs=\4/') $(cut -d' ' -f1-4 groups/sg_$g.name)"
done
