#!/bin/bash
# hd5_grow.sh: one growth pass over friendly sets of the five-level relaxed construction (job d7-family, 2026-10-25).
# For each named set, in order: pairing mask, protect list and forbidden meeting cells from the current state
# (hd5_masks.py), then dpack (1-defective ILS) from the current set; the set file is replaced by the result.
# usage: hd5_grow.sh HEXBIN STATEDIR SECONDS SEED SET [SET ...]      (DPACK = path of the dpack binary)
set -e
D=$(dirname "$(readlink -f "$0")"); HEX=$1; SD=$2; SECS=$3; SEED=$4; shift 4
DPACK=${DPACK:-$D/dpack}
for s in "$@"; do
  k=${s:0:1}
  python3 $D/hd5_masks.py $HEX $SD $s $SD/allow_$s.txt $SD/prot_$s.txt $SD/forb_$s.txt
  $DPACK $HEX $k $SEED $SECS $SD/$s.txt $SD/allow_$s.txt 0 $SD/new_$s.txt $SD/prot_$s.txt $SD/forb_$s.txt > $SD/dp_$s.log 2> $SD/dp_$s.err
  cat $SD/dp_$s.log
  mv $SD/new_$s.txt $SD/$s.txt
  SEED=$((SEED + 1))
done
