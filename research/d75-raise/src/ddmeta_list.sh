#!/bin/bash
# ddmeta_list.sh LIST OUT: run dd_meta one M K R for every "n m k r" line of LIST (formula-only metacyclic C_m : C_k)
cd "$(dirname "$0")/.."
while read n m k r; do
  echo "$n $m $k $r $(timeout 300 nice -n 8 src/dd_meta one $m $k $r logs/ddmeta 2>&1 | grep -E '^GROUP|VALID' | tr '\n' ' ')" >> "$2"
done < "$1"
echo "LISTDONE" >> "$2"
