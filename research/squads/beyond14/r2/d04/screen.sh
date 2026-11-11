#!/bin/bash
# usage: screen.sh SECS SEED TAG spec... ; spec = meta:m:k:r  (one table per group, id 1)
SECS=$1; SEED=$2; TAG=$3; shift 3
OWN=/home/user/degree-diameter/research/squads/beyond14/r2/d04
OS=/home/user/degree-diameter/research/frontier/beyond14/ownsmall
for spec in "$@"; do
  nm=$(echo "$spec" | tr ':' '_')
  T=$OWN/tabs/$nm.txt
  [ -s "$T" ] || python3 $OS/mktab.py $T "$spec" > /dev/null
  N=$(head -1 $T | awk '{print $2}')
  D=14 $OWN/salift_s 3 $T 1 $SEED $SECS 10 0.3 $OWN/sols/${TAG}_${nm}_s$SEED.sol > $OWN/logs/${TAG}_${nm}_s$SEED.log 2>&1
  echo "N=$N $spec seed=$SEED: $(tail -1 $OWN/logs/${TAG}_${nm}_s$SEED.log) | $(grep -c best $OWN/logs/${TAG}_${nm}_s$SEED.log) improvements | last: $(grep best $OWN/logs/${TAG}_${nm}_s$SEED.log | tail -1)"
done
