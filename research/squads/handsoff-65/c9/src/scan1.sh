#!/bin/sh
# scan1.sh BASE TABLE_DIR ORDER SECS SEED TAG : tabu INIT=random over every group table of ORDER in TABLE_DIR
# writes runs/TAG.tsv lines: ORDER gid name best steps; edge lists for cost 0 go to runs/TAG.g<gid>.sol
B=$1; TD=$2; O=$3; SECS=$4; SEED=$5; TAG=$6
D=$(dirname "$0")/..
cd "$D" || exit 1
mkdir -p runs
for f in $TD/sg_${O}_*.txt; do
  g=$(basename "$f" .txt); gid=${g##*_}
  name=$(cat "$TD/$g.name" 2>/dev/null | cut -d' ' -f1-3)
  out=$(INIT=random SECS=$SECS SEED=$SEED timeout 300 nice -n 10 ../shared/tabu "$B" "$f" runs/$TAG.g$gid.sol 2>/dev/null | grep RESULT)
  printf '%s\t%s\t%s\t%s\n' "$O" "$gid" "$name" "$out" >> runs/$TAG.tsv
done
