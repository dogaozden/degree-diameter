#!/bin/bash
# big.sh (card B3): one random pgl instance with 1,747,200 vertices (below the 2M build_haar2 limit).
# Checker ecc with D = 99, then both tools on the tight-D copy (must be VALID with the same ecc values).
cd "$(dirname "$0")" || exit 1
CHK=./haarcheck_pgl
BH=/home/user/degree-diameter/research/frontier/build_haar2.py
B=big/rnd_p13_n400_d11_D99.txt
$CHK "$B" > big/chk_D99.log 2>&1
eA=$(grep -o 'ecc from A = [0-9]*' big/chk_D99.log | grep -o '[0-9]*$')
eB=$(grep -o 'ecc from B = [0-9]*' big/chk_D99.log | grep -o '[0-9]*$')
dt=$(( eA > eB ? eA : eB ))
T=big/rnd_p13_n400_d11_D${dt}.txt
awk -v D="$dt" 'NR==1{$2=D}1' "$B" > "$T"
echo "big: checker D=99 -> $(tail -n 1 big/chk_D99.log); tight D=$dt"
t0=$(date +%s.%N); $CHK "$T" > big/chk_tight.log 2>&1; rc=$?; t1=$(date +%s.%N)
echo "tight: checker rc=$rc $(tail -n 1 big/chk_tight.log) time=$(awk -v a="$t0" -v b="$t1" 'BEGIN{printf "%.1fs", b-a}')"
python3 -I "$BH" "$T" > big/bh2_tight.log 2>&1; rb=$?
echo "tight: build_haar2 rc=$rb $(grep -E '^(VALID|INVALID)' big/bh2_tight.log) $(grep -o 'ecc from [AB] = [0-9]*' big/bh2_tight.log | tr '\n' ' ')"
