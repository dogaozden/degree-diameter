#!/bin/bash
# batch.sh: for every base/*.txt: exact ecc from the checker, variants in tests/, then build_haar2.py and
# haarcheck_pgl on every tests/*.txt.  Prints one line per test and "AGREE"/"DISAGREE" per file.
cd "$(dirname "$0")" || exit 1
CHK=./haarcheck_pgl
BH=/home/user/degree-diameter/research/frontier/build_haar2.py
mkdir -p tests
for b in base/*.txt; do
  eA=$($CHK "$b" | grep -o 'ecc from A = [0-9]*' | grep -o '[0-9]*$')
  eB=$($CHK "$b" | grep -o 'ecc from B = [0-9]*' | grep -o '[0-9]*$')
  if [ -z "$eA" ] || [ -z "$eB" ]; then echo "$b: checker gave no ecc"; continue; fi
  dt=$(( eA > eB ? eA : eB ))
  echo "$b: checker ecc A=$eA B=$eB -> tight D=$dt"
  python3 -I mk_variants.py "$b" tests "$dt"
done
for f in tests/*.txt; do
  python3 -I "$BH" "$f" > "${f%.txt}.bh2.log" 2>&1; rb=$?
  "$CHK" "$f" > "${f%.txt}.chk.log" 2>&1; rc=$?
  bA=$(grep -o 'ecc from A = [0-9]*' "${f%.txt}.bh2.log" | grep -o '[0-9]*$')
  bB=$(grep -o 'ecc from B = [0-9]*' "${f%.txt}.bh2.log" | grep -o '[0-9]*$')
  bl=$(grep -E '^(VALID|INVALID)' "${f%.txt}.bh2.log" | tail -n 1)
  cl=$(tail -n 1 "${f%.txt}.chk.log")
  bstat=$(echo "$bl" | cut -d' ' -f1); cstat=$(echo "$cl" | cut -d' ' -f1)
  [ -z "$bstat" ] && bstat=REJECTED
  ecc_ok=""; if [ -n "$bA" ] && [ "$bA" = "$(grep -o 'eccA=[0-9]*' <<<"$cl" | cut -d= -f2)" ] && [ "$bB" = "$(grep -o 'eccB=[0-9]*' <<<"$cl" | cut -d= -f2)" ]; then ecc_ok=" ecc-match"; fi
  if [ "$bstat" = "$cstat" ] || { [ "$bstat" = REJECTED ] && [ "$cstat" = INVALID ]; }; then ag=AGREE; else ag=DISAGREE; fi
  echo "$(basename "$f") | build_haar2 rc=$rb: ${bl:-no VALID/INVALID line (exception?)} | checker rc=$rc: $cl |$ag$ecc_ok"
done
