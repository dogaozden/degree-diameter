#!/bin/bash
# lscreen.sh LIST SECS: 2+2 lift screen (lift22, a = 1, 2, 3, seed 1) over "N ID ..." lines; log logs/lscreen.txt
cd "$(dirname "$0")/.."
T=/tmp/d75l; mkdir -p $T cand
while read N ID rest; do
  F=$T/g${N}_${ID}.ht
  timeout 600 gap -q -c "N:=$N;; ID:=$ID;; OUT:=\"$F\";; NOAUT:=true;;" src/export.g > /dev/null 2>&1
  [ -s $F ] || { echo "$N $ID GAPFAIL" >> logs/lscreen.txt; continue; }
  for a in 1 2 3; do
    r=$(SECS=$2 SEED=1 nice -n 5 src/lift22 $F $a cand/lift_${N}_${ID}_a$a.edges | tail -1)
    echo "$N $ID a $a $rest $r" >> logs/lscreen.txt
  done
  rm -f $F
done < "$1"
echo "LSCREEN DONE $1" >> logs/lscreen.txt
